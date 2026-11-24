// sosd_bench.cpp -- Comprehensive C++17 benchmark suite for
// "The Anatomy of Piecewise-Linear Learned Indexes":
//   1. Single-layer fitter spectrum (ALG-OPT, Anchored, ShrinkingCone,
//      GreedySplineCorridor / RadixSpline, Native Swing) on synthetic & SOSD data
//   2. Native Swing three-regime & alternating parity brackets on Gaussian walks
//   3. Multi-layer EP-PGM vs RE-PGM vs Flat Key-Space Bins on all four SOSD 200M
//      uint64 datasets (height H, upper-layer sizes, relative gap variance v_l,
//      Lemma 5.1 empirical boundary crossings b_l < 1, exact key comparisons,
//      auxiliary space, build time, and lookup latency)
//
// Build:
//   g++ -O3 -march=native -std=c++17 reproduce/sosd_bench.cpp -o reproduce/sosd_bench

#include <algorithm>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <random>
#include <string>
#include <vector>

namespace {

using u64 = std::uint64_t;
using i64 = std::int64_t;
using i128 = __int128_t;

constexpr double kKappaOpt = 3.53841980;
constexpr double kAlphaOpt = 0.17815941;
constexpr double kKappaAn = 2.55767103;

// Exact rational slope num / den with den > 0, |num| < 2^32, den < 2^64.
// Cross-multiplication uses signed 128-bit integers (|num * den| < 2^96 < 2^127).
struct RatSlope {
    i64 num;
    u64 den;
};

inline bool slope_lt(const RatSlope& a, const RatSlope& b) {
    return static_cast<i128>(a.num) * static_cast<i128>(b.den) <
           static_cast<i128>(b.num) * static_cast<i128>(a.den);
}

inline bool slope_le(const RatSlope& a, const RatSlope& b) {
    return static_cast<i128>(a.num) * static_cast<i128>(b.den) <=
           static_cast<i128>(b.num) * static_cast<i128>(a.den);
}

inline bool slope_gt(const RatSlope& a, const RatSlope& b) {
    return slope_lt(b, a);
}

struct HullPt {
    u64 dx;  // keys[idx] - keys[s]
    i64 y;   // (idx - s) +- eps
};

struct CompactSeg {
    u64 key_start;
    u64 key_last;
    long double slope;
    long double intercept;
    std::uint32_t start;
    std::uint32_t end;
};

// ============================================================================
// 1. Exact O(n) O'Rourke Shrinking-Cone Segmentation (ALG-OPT) on uint64 keys
// ============================================================================
std::vector<CompactSeg> alg_opt_u64(const u64* keys, std::size_t n, i64 eps, bool fit_models = true) {
    assert(n >= 1 && eps >= 1);
    std::vector<CompactSeg> segs;
    segs.reserve(n / static_cast<std::size_t>(std::max<i64>(2, eps * eps)) + 16);

    std::vector<HullPt> uh;
    std::vector<HullPt> lh;
    uh.reserve(256);
    lh.reserve(256);

    std::size_t s = 0;
    while (s < n) {
        if (s + 1 >= n) {
            segs.push_back({keys[s], keys[s], 0.0L, 0.0L,
                            static_cast<std::uint32_t>(s), static_cast<std::uint32_t>(n)});
            break;
        }

        const u64 base_x = keys[s];
        uh.clear();
        lh.clear();
        uh.push_back({0ULL, eps});
        lh.push_back({0ULL, -eps});
        std::size_t uh_ptr = 0;
        std::size_t lh_ptr = 0;
        bool has_bounds = false;
        RatSlope s_min{0, 1};
        RatSlope s_max{0, 1};

        std::size_t e = s + 1;
        while (e < n) {
            const i64 k = static_cast<i64>(e - s);
            const u64 dx = keys[e] - base_x;
            assert(dx > 0);
            const HullPt u_pt{dx, k + eps};
            const HullPt l_pt{dx, k - eps};

            while (uh_ptr + 1 < uh.size()) {
                const HullPt& p0 = uh[uh_ptr];
                const HullPt& p1 = uh[uh_ptr + 1];
                if (static_cast<i128>(l_pt.y - p1.y) * static_cast<i128>(dx - p0.dx) >=
                    static_cast<i128>(l_pt.y - p0.y) * static_cast<i128>(dx - p1.dx)) {
                    ++uh_ptr;
                } else {
                    break;
                }
            }
            const RatSlope cand_min{l_pt.y - uh[uh_ptr].y, dx - uh[uh_ptr].dx};

            while (lh_ptr + 1 < lh.size()) {
                const HullPt& p0 = lh[lh_ptr];
                const HullPt& p1 = lh[lh_ptr + 1];
                if (static_cast<i128>(u_pt.y - p1.y) * static_cast<i128>(dx - p0.dx) <=
                    static_cast<i128>(u_pt.y - p0.y) * static_cast<i128>(dx - p1.dx)) {
                    ++lh_ptr;
                } else {
                    break;
                }
            }
            const RatSlope cand_max{u_pt.y - lh[lh_ptr].y, dx - lh[lh_ptr].dx};

            const RatSlope next_min = (!has_bounds || slope_gt(cand_min, s_min)) ? cand_min : s_min;
            const RatSlope next_max = (!has_bounds || slope_lt(cand_max, s_max)) ? cand_max : s_max;
            if (slope_gt(next_min, next_max)) {
                break;
            }
            s_min = next_min;
            s_max = next_max;
            has_bounds = true;

            while (uh.size() >= 2) {
                const HullPt& p0 = uh[uh.size() - 2];
                const HullPt& p1 = uh[uh.size() - 1];
                if (static_cast<i128>(p1.y - p0.y) * static_cast<i128>(dx - p0.dx) >=
                    static_cast<i128>(u_pt.y - p0.y) * static_cast<i128>(p1.dx - p0.dx)) {
                    uh.pop_back();
                } else {
                    break;
                }
            }
            if (uh_ptr >= uh.size()) {
                uh_ptr = uh.size() - 1;
            }
            uh.push_back(u_pt);

            while (lh.size() >= 2) {
                const HullPt& p0 = lh[lh.size() - 2];
                const HullPt& p1 = lh[lh.size() - 1];
                if (static_cast<i128>(p1.y - p0.y) * static_cast<i128>(dx - p0.dx) <=
                    static_cast<i128>(l_pt.y - p0.y) * static_cast<i128>(p1.dx - p0.dx)) {
                    lh.pop_back();
                } else {
                    break;
                }
            }
            if (lh_ptr >= lh.size()) {
                lh_ptr = lh.size() - 1;
            }
            lh.push_back(l_pt);

            ++e;
        }

        long double slope = 0.0L;
        long double intercept = 0.0L;
        if (fit_models && e > s + 1) {
            const long double lo = std::max<long double>(
                0.0L, static_cast<long double>(s_min.num) / static_cast<long double>(s_min.den));
            const long double hi =
                static_cast<long double>(s_max.num) / static_cast<long double>(s_max.den);
            slope = 0.5L * (lo + hi);
            long double r_min = 0.0L;
            long double r_max = 0.0L;
            for (std::size_t idx = s + 1; idx < e; ++idx) {
                const long double x_rel = static_cast<long double>(keys[idx] - base_x);
                const long double resid = static_cast<long double>(idx - s) - slope * x_rel;
                if (resid < r_min) r_min = resid;
                if (resid > r_max) r_max = resid;
            }
            intercept = 0.5L * (r_min + r_max);
            assert(0.5L * (r_max - r_min) <= static_cast<long double>(eps) + 1e-7L);
        }
        segs.push_back({base_x, keys[e - 1], slope, intercept,
                        static_cast<std::uint32_t>(s), static_cast<std::uint32_t>(e)});
        s = e;
    }
    return segs;
}

// ============================================================================
// 2. Streaming One-Pass Fitters (Section 3.2)
// ============================================================================

// Data-anchored free-slope cone (ALG-ANCHORED)
std::size_t count_anchored_u64(const u64* keys, std::size_t n, i64 eps) {
    std::size_t count = 0;
    std::size_t s = 0;
    while (s < n) {
        ++count;
        if (s + 1 >= n) break;
        const u64 base_x = keys[s];
        RatSlope s_min{-eps + 1, keys[s + 1] - base_x};
        RatSlope s_max{eps + 1, keys[s + 1] - base_x};
        std::size_t e = s + 2;
        while (e < n) {
            const i64 k = static_cast<i64>(e - s);
            const u64 dx = keys[e] - base_x;
            const RatSlope c_min{k - eps, dx};
            const RatSlope c_max{k + eps, dx};
            const RatSlope n_min = slope_gt(c_min, s_min) ? c_min : s_min;
            const RatSlope n_max = slope_lt(c_max, s_max) ? c_max : s_max;
            if (slope_gt(n_min, n_max)) break;
            s_min = n_min;
            s_max = n_max;
            ++e;
        }
        s = e;
    }
    return count;
}

// FITing-Tree ShrinkingCone (prefix-chord fitter restarting at rejected k)
std::size_t count_shrinking_cone_u64(const u64* keys, std::size_t n, i64 eps) {
    std::size_t count = 0;
    std::size_t s = 0;
    while (s < n) {
        ++count;
        if (s + 1 >= n) break;
        const u64 base_x = keys[s];
        RatSlope s_min{1 - eps, keys[s + 1] - base_x};
        RatSlope s_max{1 + eps, keys[s + 1] - base_x};
        std::size_t e = s + 2;
        while (e < n) {
            const i64 k = static_cast<i64>(e - s);
            const u64 dx = keys[e] - base_x;
            const RatSlope chord{k, dx};
            if (slope_lt(chord, s_min) || slope_gt(chord, s_max)) break;
            const RatSlope c_min{k - eps, dx};
            const RatSlope c_max{k + eps, dx};
            if (slope_gt(c_min, s_min)) s_min = c_min;
            if (slope_lt(c_max, s_max)) s_max = c_max;
            ++e;
        }
        s = e;
    }
    return count;
}

// RadixSpline GreedySplineCorridor (prefix-chord fitter restarting at k-1 and carrying k)
std::size_t count_radix_spline_u64(const u64* keys, std::size_t n, i64 eps) {
    if (n <= 2) return 1;
    std::size_t spans = 0;
    std::size_t s = 0;
    u64 base_x = keys[0];
    RatSlope s_min{1 - eps, keys[1] - base_x};
    RatSlope s_max{1 + eps, keys[1] - base_x};
    for (std::size_t k_idx = 2; k_idx < n; ++k_idx) {
        const i64 k = static_cast<i64>(k_idx - s);
        const u64 dx = keys[k_idx] - base_x;
        const RatSlope chord{k, dx};
        if (slope_lt(chord, s_min) || slope_gt(chord, s_max)) {
            ++spans;
            s = k_idx - 1;
            base_x = keys[s];
            const u64 dx1 = keys[k_idx] - base_x;
            s_min = {1 - eps, dx1};
            s_max = {1 + eps, dx1};
        } else {
            const RatSlope c_min{k - eps, dx};
            const RatSlope c_max{k + eps, dx};
            if (slope_gt(c_min, s_min)) s_min = c_min;
            if (slope_lt(c_max, s_max)) s_max = c_max;
        }
    }
    ++spans;
    return spans;
}

// Native Swing filter (Elmeleegy et al. PVLDB 2009; formalized in Stream.lean & ConstrainedSSE.lean)
std::size_t count_native_swing_u64(const u64* keys, std::size_t n, i64 eps) {
    if (n <= 2) return 1;
    const long double e_ld = static_cast<long double>(eps);
    std::size_t segs = 0;
    std::size_t s = 0;
    std::size_t e = 1;
    long double q_rel = 0.0L;  // anchorValue - s (relative to true rank s, so |q_rel| <= eps)
    long double dt1 = static_cast<long double>(keys[1] - keys[0]);
    long double L = (1.0L - q_rel - e_ld) / dt1;
    long double U = (1.0L - q_rel + e_ld) / dt1;
    long double S_tx = dt1 * (1.0L - q_rel);
    long double S_tt = dt1 * dt1;

    while (e + 1 < n) {
        const std::size_t nxt = e + 1;
        const long double dt = static_cast<long double>(keys[nxt] - keys[s]);
        const long double dy = static_cast<long double>(nxt - s) - q_rel;
        const long double cL = (dy - e_ld) / dt;
        const long double cU = (dy + e_ld) / dt;
        const long double nL = std::max(L, cL);
        const long double nU = std::min(U, cU);
        if (nL <= nU) {
            L = nL;
            U = nU;
            S_tx += dt * dy;
            S_tt += dt * dt;
            e = nxt;
        } else {
            ++segs;
            const long double m_ls = S_tx / S_tt;
            const long double m_sel = std::max(L, std::min(m_ls, U));
            const long double dt_end = static_cast<long double>(keys[e] - keys[s]);
            // Fitted value at e is s + q_rel + m_sel * dt_end; subtract new start rank e:
            q_rel = q_rel + m_sel * dt_end - static_cast<long double>(e - s);
            s = e;
            e = nxt;
            const long double dt_init = static_cast<long double>(keys[e] - keys[s]);
            const long double dy_init = 1.0L - q_rel;
            L = (dy_init - e_ld) / dt_init;
            U = (dy_init + e_ld) / dt_init;
            S_tx = dt_init * dy_init;
            S_tt = dt_init * dt_init;
        }
    }
    ++segs;
    return segs;
}

// ============================================================================
// 3. Complete EP-PGM and RE-PGM Index Structures with Exact Predecessor Search
// ============================================================================

struct EPLayer {
    const u64* keys_ptr = nullptr;
    std::size_t n_keys = 0;
    std::vector<u64> owned_pivots;
    std::vector<CompactSeg> segs;
};

class EPPGMIndex {
public:
    i64 eps;
    std::vector<EPLayer> layers;

    EPPGMIndex(const std::vector<u64>& base_keys, i64 eps_) : eps(eps_) {
        if (base_keys.size() <= 1) return;
        EPLayer base_layer;
        base_layer.keys_ptr = base_keys.data();
        base_layer.n_keys = base_keys.size();
        base_layer.segs = alg_opt_u64(base_layer.keys_ptr, base_layer.n_keys, eps, true);
        const std::size_t m1 = base_layer.segs.size();
        layers.push_back(std::move(base_layer));
        if (m1 <= 1) return;

        std::vector<u64> tmp(m1);
        for (std::size_t j = 0; j < m1; ++j) {
            tmp[j] = layers[0].segs[j].key_start;
        }
        while (tmp.size() > 1) {
            EPLayer ul;
            ul.owned_pivots = std::move(tmp);
            ul.n_keys = ul.owned_pivots.size();
            ul.segs = alg_opt_u64(ul.owned_pivots.data(), ul.n_keys, eps, true);
            const std::size_t um = ul.segs.size();
            layers.push_back(std::move(ul));
            layers.back().keys_ptr = layers.back().owned_pivots.data();
            if (um <= 1) break;
            tmp.resize(um);
            for (std::size_t j = 0; j < um; ++j) {
                tmp[j] = layers.back().segs[j].key_start;
            }
        }
    }

    int height() const { return static_cast<int>(layers.size()); }

    std::size_t aux_bytes() const {
        // Canonical PGM: 24B per segment (uint64 key_start, uint32 start, float intercept, double slope)
        std::size_t total_segs = 0;
        for (const auto& l : layers) total_segs += l.segs.size();
        return total_segs * 24ULL;
    }

    std::int64_t predecessor(u64 q, std::uint64_t& cmp_count) const {
        if (q < layers[0].keys_ptr[0]) {
            ++cmp_count;
            return -1;
        }
        std::size_t seg_idx = 0;  // Top layer has M_H = 1 segment
        for (int l = static_cast<int>(layers.size()) - 1; l >= 0; --l) {
            const EPLayer& layer = layers[l];
            const CompactSeg& seg = layer.segs[seg_idx];
            const u64 z = std::min(q, seg.key_last);
            const i64 pred_local = static_cast<i64>(
                std::floor(seg.slope * static_cast<long double>(z - seg.key_start) + seg.intercept));
            const i64 pred = static_cast<i64>(seg.start) + pred_local;
            const i64 lo = static_cast<i64>(seg.start);
            // Under EP, segment seg_idx covers up to next segment's start - 1 (which equals seg.end - 1)
            const i64 hi = static_cast<i64>(seg.end) - 1;
            const i64 clamped = std::min(std::max(pred, lo), hi);
            std::size_t w_lo = static_cast<std::size_t>(std::max(lo, clamped - eps - 1));
            std::size_t w_hi = static_cast<std::size_t>(std::min(hi, clamped + eps + 1));

            // Binary search largest index in [w_lo, w_hi] with keys_ptr[idx] <= q
            const u64* kp = layer.keys_ptr;
            std::size_t left = w_lo;
            std::size_t right = w_hi + 1;
            while (left < right) {
                const std::size_t mid = left + ((right - left) >> 1);
                ++cmp_count;
                if (kp[mid] <= q) {
                    left = mid + 1;
                } else {
                    right = mid;
                }
            }
            seg_idx = left - 1;
        }
        return static_cast<std::int64_t>(seg_idx);
    }

    // Fast path without comparison counter for latency benchmarking
    std::int64_t predecessor_fast(u64 q) const {
        if (q < layers[0].keys_ptr[0]) return -1;
        std::size_t seg_idx = 0;
        for (int l = static_cast<int>(layers.size()) - 1; l >= 0; --l) {
            const EPLayer& layer = layers[l];
            const CompactSeg& seg = layer.segs[seg_idx];
            const u64 z = std::min(q, seg.key_last);
            const i64 pred_local = static_cast<i64>(
                std::floor(seg.slope * static_cast<long double>(z - seg.key_start) + seg.intercept));
            const i64 pred = static_cast<i64>(seg.start) + pred_local;
            const i64 lo = static_cast<i64>(seg.start);
            const i64 hi = static_cast<i64>(seg.end) - 1;
            const i64 clamped = std::min(std::max(pred, lo), hi);
            std::size_t left = static_cast<std::size_t>(std::max(lo, clamped - eps - 1));
            std::size_t right = static_cast<std::size_t>(std::min(hi, clamped + eps + 1)) + 1;
            const u64* kp = layer.keys_ptr;
            while (left < right) {
                const std::size_t mid = left + ((right - left) >> 1);
                if (kp[mid] <= q) left = mid + 1;
                else right = mid;
            }
            seg_idx = left - 1;
        }
        return static_cast<std::int64_t>(seg_idx);
    }
};

struct BucketHdr {
    std::uint32_t left_seg;
    std::uint32_t offset;
};

struct RELayer {
    const u64* keys_ptr = nullptr;
    std::size_t n_keys = 0;
    std::vector<u64> owned_pivots;
    std::size_t delta = 1;
    std::size_t d_stride = 1;
    std::vector<CompactSeg> segs;
    std::vector<BucketHdr> buckets;  // size N_{l+1} + 1 (sentinel offset at end)
    std::vector<u64> boundary_keys;  // size <= M_{l+1} - 1
};

class REPGMIndex {
public:
    i64 eps;
    std::vector<RELayer> layers;

    REPGMIndex(const std::vector<u64>& base_keys, i64 eps_) : eps(eps_) {
        std::vector<u64> cur_owned;
        std::size_t delta = 1;
        bool is_base = true;

        while (true) {
            RELayer layer;
            if (is_base) {
                layer.keys_ptr = base_keys.data();
                layer.n_keys = base_keys.size();
            } else {
                layer.owned_pivots = std::move(cur_owned);
                layer.keys_ptr = layer.owned_pivots.data();
                layer.n_keys = layer.owned_pivots.size();
            }
            const std::size_t n_l = layer.n_keys;
            if (n_l <= 1) break;

            layer.delta = delta;
            layer.segs = alg_opt_u64(layer.keys_ptr, n_l, eps, true);
            const std::size_t m_next = layer.segs.size();
            const std::size_t d_l = n_l / m_next;
            assert(d_l >= 1);
            const std::size_t n_next = (n_l + d_l - 1) / d_l;
            layer.d_stride = d_l;

            layer.buckets.resize(n_next + 1);
            layer.boundary_keys.reserve(m_next);

            std::size_t seg_idx = 0;
            for (std::size_t j = 0; j < n_next; ++j) {
                const std::size_t left_rank = j * d_l;
                const std::size_t right_rank = (j + 1 < n_next) ? (j + 1) * d_l : n_l;
                while (seg_idx + 1 < m_next && layer.segs[seg_idx + 1].start <= left_rank) {
                    ++seg_idx;
                }
                layer.buckets[j] = {static_cast<std::uint32_t>(seg_idx),
                                    static_cast<std::uint32_t>(layer.boundary_keys.size())};
                std::size_t m_scan = seg_idx + 1;
                while (m_scan < m_next && layer.segs[m_scan].start < right_rank) {
                    layer.boundary_keys.push_back(layer.keys_ptr[layer.segs[m_scan].start]);
                    ++m_scan;
                }
            }
            layer.buckets[n_next] = {static_cast<std::uint32_t>(m_next),
                                     static_cast<std::uint32_t>(layer.boundary_keys.size())};

            if (n_next > 1) {
                cur_owned.resize(n_next);
                for (std::size_t j = 0; j < n_next; ++j) {
                    cur_owned[j] = layer.keys_ptr[j * d_l];
                }
            }
            layers.push_back(std::move(layer));
            if (!is_base) {
                layers.back().keys_ptr = layers.back().owned_pivots.data();
            }
            delta *= d_l;
            is_base = false;
            if (n_next <= 1) break;
        }
    }

    int height() const { return static_cast<int>(layers.size()); }

    std::size_t aux_bytes() const {
        // Segments (16B without key_start if key_start is in boundary/pivots, or 24B matched)
        // + promoted pivots (8B * owned_pivots) + CSR headers (8B * N_{l+1}) + boundary_keys (8B)
        std::size_t bytes = 0;
        for (const auto& l : layers) {
            bytes += l.segs.size() * 24ULL;
            bytes += l.owned_pivots.size() * 8ULL;
            bytes += l.buckets.size() * sizeof(BucketHdr);
            bytes += l.boundary_keys.size() * 8ULL;
        }
        return bytes;
    }

    std::int64_t predecessor(u64 q, std::uint64_t& cmp_count) const {
        if (q < layers[0].keys_ptr[0]) {
            ++cmp_count;
            return -1;
        }
        std::size_t j = 0;  // Singleton root bucket
        for (int l = static_cast<int>(layers.size()) - 1; l >= 0; --l) {
            const RELayer& layer = layers[l];
            const std::uint32_t b_start = layer.buckets[j].offset;
            const std::uint32_t b_end = layer.buckets[j + 1].offset;
            std::size_t seg_id = layer.buckets[j].left_seg;
            if (b_start < b_end) {
                std::uint32_t bl = b_start;
                std::uint32_t br = b_end;
                const u64* bk = layer.boundary_keys.data();
                while (bl < br) {
                    const std::uint32_t mid = bl + ((br - bl) >> 1);
                    ++cmp_count;
                    if (bk[mid] <= q) bl = mid + 1;
                    else br = mid;
                }
                seg_id += (bl - b_start);
            }

            const CompactSeg& seg = layer.segs[seg_id];
            const u64 z = std::min(q, seg.key_last);
            const i64 pred_local = static_cast<i64>(
                std::floor(seg.slope * static_cast<long double>(z - seg.key_start) + seg.intercept));
            const i64 pred = static_cast<i64>(seg.start) + pred_local;

            const i64 lo_b = static_cast<i64>(j * layer.d_stride);
            const i64 hi_b = static_cast<i64>(
                std::min(layer.n_keys, (j + 1) * layer.d_stride)) - 1;
            const i64 lo = std::max(static_cast<i64>(seg.start), lo_b);
            const i64 hi = std::min(static_cast<i64>(seg.end) - 1, hi_b);
            const i64 clamped = std::min(std::max(pred, lo), hi);

            std::size_t left = static_cast<std::size_t>(std::max(lo, clamped - eps - 1));
            std::size_t right = static_cast<std::size_t>(std::min(hi, clamped + eps + 1)) + 1;
            const u64* kp = layer.keys_ptr;
            while (left < right) {
                const std::size_t mid = left + ((right - left) >> 1);
                ++cmp_count;
                if (kp[mid] <= q) left = mid + 1;
                else right = mid;
            }
            j = left - 1;
        }
        return static_cast<std::int64_t>(j);
    }

    std::int64_t predecessor_fast(u64 q) const {
        if (q < layers[0].keys_ptr[0]) return -1;
        std::size_t j = 0;
        for (int l = static_cast<int>(layers.size()) - 1; l >= 0; --l) {
            const RELayer& layer = layers[l];
            const std::uint32_t b_start = layer.buckets[j].offset;
            const std::uint32_t b_end = layer.buckets[j + 1].offset;
            std::size_t seg_id = layer.buckets[j].left_seg;
            if (b_start < b_end) {
                std::uint32_t bl = b_start;
                std::uint32_t br = b_end;
                const u64* bk = layer.boundary_keys.data();
                while (bl < br) {
                    const std::uint32_t mid = bl + ((br - bl) >> 1);
                    if (bk[mid] <= q) bl = mid + 1;
                    else br = mid;
                }
                seg_id += (bl - b_start);
            }

            const CompactSeg& seg = layer.segs[seg_id];
            const u64 z = std::min(q, seg.key_last);
            const i64 pred_local = static_cast<i64>(
                std::floor(seg.slope * static_cast<long double>(z - seg.key_start) + seg.intercept));
            const i64 pred = static_cast<i64>(seg.start) + pred_local;

            const i64 lo_b = static_cast<i64>(j * layer.d_stride);
            const i64 hi_b = static_cast<i64>(
                std::min(layer.n_keys, (j + 1) * layer.d_stride)) - 1;
            const i64 lo = std::max(static_cast<i64>(seg.start), lo_b);
            const i64 hi = std::min(static_cast<i64>(seg.end) - 1, hi_b);
            const i64 clamped = std::min(std::max(pred, lo), hi);

            std::size_t left = static_cast<std::size_t>(std::max(lo, clamped - eps - 1));
            std::size_t right = static_cast<std::size_t>(std::min(hi, clamped + eps + 1)) + 1;
            const u64* kp = layer.keys_ptr;
            while (left < right) {
                const std::size_t mid = left + ((right - left) >> 1);
                if (kp[mid] <= q) left = mid + 1;
                else right = mid;
            }
            j = left - 1;
        }
        return static_cast<std::int64_t>(j);
    }
};

// ============================================================================
// 4. Utilities: SOSD Loader, Relative Variance, Lemma 5.1 & Flat Key-Space Bins
// ============================================================================

std::vector<u64> load_sosd_unique(const std::string& path, std::size_t& raw_count) {
    std::ifstream in(path, std::ios::binary);
    if (!in) {
        std::cerr << "Failed to open SOSD file: " << path << "\n";
        std::exit(1);
    }
    u64 count = 0;
    in.read(reinterpret_cast<char*>(&count), sizeof(u64));
    raw_count = static_cast<std::size_t>(count);
    std::vector<u64> keys(raw_count);
    in.read(reinterpret_cast<char*>(keys.data()), static_cast<std::streamsize>(raw_count * sizeof(u64)));
    auto it = std::unique(keys.begin(), keys.end());
    keys.erase(it, keys.end());
    return keys;
}

double rel_gap_var_u64(const u64* keys, std::size_t n) {
    if (n < 3) return 0.0;
    const std::size_t m = n - 1;
    long double sum = 0.0L;
    long double sum_sq = 0.0L;
    for (std::size_t i = 0; i < m; ++i) {
        const long double g = static_cast<long double>(keys[i + 1] - keys[i]);
        sum += g;
        sum_sq += g * g;
    }
    const long double mean = sum / static_cast<long double>(m);
    if (mean == 0.0L) return 0.0;
    const long double var = std::max(0.0L, sum_sq / static_cast<long double>(m) - mean * mean);
    return static_cast<double>(var / (mean * mean));
}

// Compute exact Lemma 5.1 stored-key average boundary crossings at layer l:
// (1/n) sum_{i=0}^{n-1} b_{l, j_l(p_i)}
double exact_lemma51_avg_b(const RELayer& layer, std::size_t total_base_n) {
    const std::size_t n_buckets = layer.buckets.size() - 1;
    const std::size_t chunk = layer.d_stride * layer.delta;
    long double weighted_sum = 0.0L;
    for (std::size_t j = 0; j < n_buckets; ++j) {
        const std::size_t lo_base = j * chunk;
        const std::size_t hi_base = std::min(total_base_n, (j + 1) * chunk);
        const std::size_t occ = hi_base - lo_base;
        const std::uint32_t b_lj = layer.buckets[j + 1].offset - layer.buckets[j].offset;
        weighted_sum += static_cast<long double>(occ) * static_cast<long double>(b_lj);
    }
    return static_cast<double>(weighted_sum / static_cast<long double>(total_base_n));
}

// Evaluate flat equal-width key-space directory with K = M_1 bins over [keys[0], keys[n-1]]
// (models RadixSpline / ESPC key-space binning under matched bin count K = M_1).
struct FlatBinStats {
    std::size_t max_segs_in_bin = 0;
    double avg_segs_queried = 0.0;
};

FlatBinStats eval_flat_key_bins(const std::vector<u64>& keys, const std::vector<CompactSeg>& segs) {
    const std::size_t n = keys.size();
    const std::size_t K = segs.size();
    if (K <= 1) return {0, 0.0};
    const long double min_k = static_cast<long double>(keys.front());
    const long double span = static_cast<long double>(keys.back() - keys.front());

    auto key_to_bin = [&](u64 k) -> std::size_t {
        if (span == 0.0L) return 0;
        const long double frac = (static_cast<long double>(k) - min_k) / span;
        std::size_t b = static_cast<std::size_t>(frac * static_cast<long double>(K));
        return (b >= K) ? (K - 1) : b;
    };

    std::vector<std::uint32_t> bin_seg_starts(K, 0);
    for (std::size_t m = 1; m < segs.size(); ++m) {
        bin_seg_starts[key_to_bin(segs[m].key_start)] += 1;
    }
    std::vector<std::size_t> bin_key_occ(K, 0);
    for (u64 k : keys) {
        bin_key_occ[key_to_bin(k)] += 1;
    }

    std::uint32_t max_b = 0;
    long double weighted = 0.0L;
    for (std::size_t b = 0; b < K; ++b) {
        if (bin_seg_starts[b] > max_b) max_b = bin_seg_starts[b];
        weighted += static_cast<long double>(bin_key_occ[b]) * static_cast<long double>(bin_seg_starts[b]);
    }
    return {max_b, static_cast<double>(weighted / static_cast<long double>(n))};
}

// ============================================================================
// 5. Subcommands
// ============================================================================

void run_synthetic_fitters() {
    std::cout << "family,eps,n,k_opt_emp,a_opt_emp,k_an_emp,k_sc_emp,k_rs_emp,swing_mean_len,swing_over_opt_segs,chord_bracket_ok\n";
    const std::size_t n = 20000000;
    for (const std::string fam : {"exp", "unif"}) {
        const double v0 = (fam == "exp") ? 1.0 : (1.0 / 3.0);
        std::mt19937_64 rng(20261124);
        std::vector<u64> keys(n);
        u64 acc = 1000;
        keys[0] = acc;
        if (fam == "exp") {
            std::exponential_distribution<double> d(1.0);
            for (std::size_t i = 1; i < n; ++i) {
                acc += std::max<u64>(1ULL, static_cast<u64>( std::llround(d(rng) * 1e9) ));
                keys[i] = acc;
            }
        } else {
            std::uniform_int_distribution<u64> d(1ULL, 2000000000ULL);
            for (std::size_t i = 1; i < n; ++i) {
                acc += d(rng);
                keys[i] = acc;
            }
        }

        for (i64 eps : {4, 8, 16, 32, 64, 128, 256}) {
            auto opt_segs = alg_opt_u64(keys.data(), n, eps, false);
            auto opt_half = alg_opt_u64(keys.data(), n, eps / 2, false);
            const std::size_t m_opt = opt_segs.size();
            const std::size_t m_opt_half = opt_half.size();
            const std::size_t m_an = count_anchored_u64(keys.data(), n, eps);
            const std::size_t m_sc = count_shrinking_cone_u64(keys.data(), n, eps);
            const std::size_t m_rs = count_radix_spline_u64(keys.data(), n, eps);
            const std::size_t m_sw = count_native_swing_u64(keys.data(), n, eps);

            // Relative stopping-length variance on interior ALG-OPT segments
            long double s1 = 0.0L, s2 = 0.0L;
            const std::size_t cnt = (m_opt > 2) ? (m_opt - 1) : m_opt;
            for (std::size_t j = 0; j < cnt; ++j) {
                const long double len = static_cast<long double>(opt_segs[j].end - opt_segs[j].start);
                s1 += len;
                s2 += len * len;
            }
            const long double mu = s1 / cnt;
            const long double var = std::max(0.0L, s2 / cnt - mu * mu);
            const double a_emp = static_cast<double>(var / (mu * mu));

            const double scale = v0 / (static_cast<double>(eps) * static_cast<double>(eps));
            const double k_opt_e = static_cast<double>(mu) * scale;
            const double k_an_e = (static_cast<double>(n) / (m_an > 1 ? m_an - 0.5 : 1.0)) * scale;
            const double k_sc_e = (static_cast<double>(n) / (m_sc > 1 ? m_sc - 0.5 : 1.0)) * scale;
            const double k_rs_e = (static_cast<double>(n) / (m_rs > 1 ? m_rs - 0.5 : 1.0)) * scale;
            const double sw_len = static_cast<double>(n) / m_sw;
            const double sw_ratio = static_cast<double>(m_sw) / static_cast<double>(m_opt);
            const int bracket_ok = (m_opt <= m_sc && m_sc <= m_opt_half) ? 1 : 0;

            std::cout << std::fixed << std::setprecision(4)
                      << fam << "," << eps << "," << n << ","
                      << k_opt_e << "," << a_emp << ","
                      << k_an_e << "," << k_sc_e << "," << k_rs_e << ","
                      << sw_len << "," << sw_ratio << "," << bracket_ok << "\n";
        }
    }
}

void run_swing_gaussian() {
    // Directly test Theorem 3.4 on i.i.d. standard Gaussian random walks:
    // L_{1,E}/E^2 -> kappa_an, L_{2,E}/E -> kappa_2, L_{k,E}/(E log E) -> c_k (alternating)
    std::cout << "E,trials,L1_over_E2,L2_over_E,c3,c4,c5,c6,c7,c8\n";
    for (double E : {32.0, 64.0, 128.0}) {
        const int trials = (E <= 64.0) ? 12000 : 6000;
        std::mt19937_64 rng(777 + static_cast<u64>(E));
        std::normal_distribution<double> norm(0.0, 1.0);
        std::vector<long double> sum_len(9, 0.0L);

        for (int tr = 0; tr < trials; ++tr) {
            long double y_cur = 0.0L;
            long double q = 0.0L;
            std::size_t s = 0;
            long double y1 = y_cur + norm(rng);
            y_cur = y1;
            std::size_t e = 1;
            long double L = (y1 - q - E);
            long double U = (y1 - q + E);
            long double S_tx = (y1 - q);
            long double S_tt = 1.0L;

            for (int seg_k = 1; seg_k <= 8; ++seg_k) {
                while (true) {
                    const std::size_t nxt = e + 1;
                    const long double y_nxt = y_cur + norm(rng);
                    const long double dt = static_cast<long double>(nxt - s);
                    const long double dy = y_nxt - q;
                    const long double nL = std::max(L, (dy - E) / dt);
                    const long double nU = std::min(U, (dy + E) / dt);
                    if (nL <= nU) {
                        L = nL;
                        U = nU;
                        S_tx += dt * dy;
                        S_tt += dt * dt;
                        e = nxt;
                        y_cur = y_nxt;
                    } else {
                        sum_len[seg_k] += static_cast<long double>(e - s + 1);
                        const long double m_sel = std::max(L, std::min(S_tx / S_tt, U));
                        q = q + m_sel * static_cast<long double>(e - s);
                        s = e;
                        e = nxt;
                        y_cur = y_nxt;
                        const long double dy_init = y_cur - q;
                        L = dy_init - E;
                        U = dy_init + E;
                        S_tx = dy_init;
                        S_tt = 1.0L;
                        break;
                    }
                }
            }
        }
        const double elog = E * std::log(E);
        std::cout << std::fixed << std::setprecision(4)
                  << static_cast<int>(E) << "," << trials << ","
                  << static_cast<double>(sum_len[1] / trials) / (E * E) << ","
                  << static_cast<double>(sum_len[2] / trials) / E << ","
                  << static_cast<double>(sum_len[3] / trials) / elog << ","
                  << static_cast<double>(sum_len[4] / trials) / elog << ","
                  << static_cast<double>(sum_len[5] / trials) / elog << ","
                  << static_cast<double>(sum_len[6] / trials) / elog << ","
                  << static_cast<double>(sum_len[7] / trials) / elog << ","
                  << static_cast<double>(sum_len[8] / trials) / elog << "\n";
    }
}

void run_sosd_all(const std::string& data_dir) {
    const std::vector<std::pair<std::string, std::string>> datasets = {
        {"books", data_dir + "/books_200M_uint64"},
        {"fb", data_dir + "/fb_200M_uint64"},
        {"osm", data_dir + "/osm_cellids_200M_uint64"},
        {"wiki", data_dir + "/wiki_ts_200M_uint64"},
    };

    std::ofstream f_hier("reproduce/data/sosd_hierarchy_routing.csv");
    std::ofstream f_fit("reproduce/data/sosd_fitters.csv");

    f_hier << "dataset,raw_n,unique_n,eps,M1,"
           << "H_ep,N2_ep,N3_ep,v0,v1_ep,v2_ep,"
           << "H_re,N2_re,N3_re,v1_re,v2_re,"
           << "max_avg_b_re,b0_re,b1_re,"
           << "cmp_ep,cmp_re,bytes_per_key_ep,bytes_per_key_re,"
           << "build_s_ep,build_s_re,ns_ep,ns_re,"
           << "flat_max_segs_in_bin,flat_avg_segs_queried\n";

    f_fit << "dataset,unique_n,eps,M_opt,M_anchored,M_shrinking_cone,M_radix_spline,M_swing,"
          << "ratio_sc_opt,ratio_rs_opt,ratio_swing_opt,chord_bracket_ok\n";

    for (const auto& [name, path] : datasets) {
        std::ifstream test_in(path, std::ios::binary);
        if (!test_in) {
            std::cerr << "[SKIP] " << path << " not found.\n";
            continue;
        }
        test_in.close();

        std::size_t raw_n = 0;
        std::cerr << "[LOAD] Loading & deduplicating " << name << " ...\n";
        std::vector<u64> keys = load_sosd_unique(path, raw_n);
        const std::size_t n = keys.size();
        const double v0 = rel_gap_var_u64(keys.data(), n);
        std::cerr << "[INFO] " << name << ": raw=" << raw_n << ", unique=" << n
                  << ", v0=" << v0 << "\n";

        // Prepare 1,000,000 uniformly sampled stored-key queries + edge queries for verification & timing
        const std::size_t n_queries = 1000000;
        std::mt19937_64 qrng(20261124);
        std::uniform_int_distribution<std::size_t> qpick(0, n - 1);
        std::vector<u64> queries(n_queries);
        std::vector<std::int64_t> expected_ranks(n_queries);
        for (std::size_t qi = 0; qi < n_queries; ++qi) {
            const std::size_t idx = qpick(qrng);
            queries[qi] = keys[idx];
            expected_ranks[qi] = static_cast<std::int64_t>(idx);
        }

        for (i64 eps : {2, 4, 8, 16, 32, 64}) {
            auto t0 = std::chrono::steady_clock::now();
            EPPGMIndex ep_idx(keys, eps);
            auto t1 = std::chrono::steady_clock::now();
            REPGMIndex re_idx(keys, eps);
            auto t2 = std::chrono::steady_clock::now();

            const double build_ep = std::chrono::duration<double>(t1 - t0).count();
            const double build_re = std::chrono::duration<double>(t2 - t1).count();

            // Verify 100% exact predecessor on all 1,000,000 random stored keys + midpoint/boundary probes
            std::uint64_t cmp_ep_tot = 0;
            std::uint64_t cmp_re_tot = 0;
            for (std::size_t qi = 0; qi < n_queries; ++qi) {
                const auto r_ep = ep_idx.predecessor(queries[qi], cmp_ep_tot);
                const auto r_re = re_idx.predecessor(queries[qi], cmp_re_tot);
                if (r_ep != expected_ranks[qi] || r_re != expected_ranks[qi]) {
                    std::cerr << "[FATAL] Predecessor mismatch on " << name << " eps=" << eps
                              << " q=" << queries[qi] << " exp=" << expected_ranks[qi]
                              << " ep=" << r_ep << " re=" << r_re << "\n";
                    std::exit(2);
                }
            }
            // Also check 5,000 non-stored midpoint/out-of-range queries against std::upper_bound
            for (std::size_t probe = 0; probe < 5000; ++probe) {
                const std::size_t idx = (probe * 39989ULL) % (n - 1);
                const u64 q_mid = keys[idx] + ((keys[idx + 1] - keys[idx]) >> 1);
                std::uint64_t dummy = 0;
                const std::int64_t gt = static_cast<std::int64_t>(
                    std::upper_bound(keys.begin(), keys.end(), q_mid) - keys.begin()) - 1;
                assert(ep_idx.predecessor(q_mid, dummy) == gt);
                assert(re_idx.predecessor(q_mid, dummy) == gt);
            }

            // Measure pure lookup latency over 2,000,000 queries (with volatile sink to prevent dead-code elim)
            volatile std::int64_t sink = 0;
            auto q_t0 = std::chrono::steady_clock::now();
            std::int64_t acc_ep = 0;
            for (std::size_t rep = 0; rep < 2; ++rep) {
                for (std::size_t qi = 0; qi < n_queries; ++qi) {
                    acc_ep ^= ep_idx.predecessor_fast(queries[qi]);
                }
            }
            auto q_t1 = std::chrono::steady_clock::now();
            std::int64_t acc_re = 0;
            for (std::size_t rep = 0; rep < 2; ++rep) {
                for (std::size_t qi = 0; qi < n_queries; ++qi) {
                    acc_re ^= re_idx.predecessor_fast(queries[qi]);
                }
            }
            auto q_t2 = std::chrono::steady_clock::now();
            sink = acc_ep ^ acc_re;
            (void)sink;
            assert(acc_ep == acc_re);

            const double ns_ep = std::chrono::duration<double, std::nano>(q_t1 - q_t0).count() / (2.0 * n_queries);
            const double ns_re = std::chrono::duration<double, std::nano>(q_t2 - q_t1).count() / (2.0 * n_queries);

            // Extract structural metrics
            const std::size_t m1 = ep_idx.layers[0].segs.size();
            auto get_ep_nl = [&](std::size_t l) -> std::size_t {
                return (l < ep_idx.layers.size()) ? ep_idx.layers[l].n_keys : 1ULL;
            };
            auto get_re_nl = [&](std::size_t l) -> std::size_t {
                return (l < re_idx.layers.size()) ? re_idx.layers[l].n_keys : 1ULL;
            };
            const double v1_ep = (ep_idx.layers.size() >= 2)
                                     ? rel_gap_var_u64(ep_idx.layers[1].keys_ptr, ep_idx.layers[1].n_keys)
                                     : 0.0;
            const double v2_ep = (ep_idx.layers.size() >= 3)
                                     ? rel_gap_var_u64(ep_idx.layers[2].keys_ptr, ep_idx.layers[2].n_keys)
                                     : 0.0;
            const double v1_re = (re_idx.layers.size() >= 2)
                                     ? rel_gap_var_u64(re_idx.layers[1].keys_ptr, re_idx.layers[1].n_keys)
                                     : 0.0;
            const double v2_re = (re_idx.layers.size() >= 3)
                                     ? rel_gap_var_u64(re_idx.layers[2].keys_ptr, re_idx.layers[2].n_keys)
                                     : 0.0;

            double max_avg_b = 0.0;
            double b0_re = 0.0;
            double b1_re = 0.0;
            for (std::size_t l = 0; l < re_idx.layers.size(); ++l) {
                const double avg_b = exact_lemma51_avg_b(re_idx.layers[l], n);
                assert(avg_b < 1.0);
                if (avg_b > max_avg_b) max_avg_b = avg_b;
                if (l == 0) b0_re = avg_b;
                if (l == 1) b1_re = avg_b;
            }

            const FlatBinStats flat_st = eval_flat_key_bins(keys, ep_idx.layers[0].segs);

            f_hier << name << "," << raw_n << "," << n << "," << eps << "," << m1 << ","
                   << ep_idx.height() << "," << get_ep_nl(2) << "," << get_ep_nl(3) << ","
                   << std::scientific << std::setprecision(3) << v0 << ","
                   << std::fixed << std::setprecision(4) << v1_ep << "," << v2_ep << ","
                   << re_idx.height() << "," << get_re_nl(2) << "," << get_re_nl(3) << ","
                   << v1_re << "," << v2_re << ","
                   << max_avg_b << "," << b0_re << "," << b1_re << ","
                   << std::setprecision(2)
                   << (static_cast<double>(cmp_ep_tot) / n_queries) << ","
                   << (static_cast<double>(cmp_re_tot) / n_queries) << ","
                   << std::setprecision(4)
                   << (static_cast<double>(ep_idx.aux_bytes()) / n) << ","
                   << (static_cast<double>(re_idx.aux_bytes()) / n) << ","
                   << std::setprecision(3) << build_ep << "," << build_re << ","
                   << std::setprecision(1) << ns_ep << "," << ns_re << ","
                   << flat_st.max_segs_in_bin << ","
                   << std::setprecision(2) << flat_st.avg_segs_queried << "\n";
            f_hier.flush();

            std::cerr << "  [" << name << " eps=" << eps << "] H_ep=" << ep_idx.height()
                      << " (N2=" << get_ep_nl(2) << ") vs H_re=" << re_idx.height()
                      << " (N2=" << get_re_nl(2) << "), b0=" << std::fixed << std::setprecision(3) << b0_re
                      << ", cmp=" << std::setprecision(2) << (double(cmp_ep_tot)/n_queries)
                      << "->" << (double(cmp_re_tot)/n_queries)
                      << ", ns=" << std::setprecision(1) << ns_ep << "/" << ns_re
                      << ", flat_max_bin=" << flat_st.max_segs_in_bin << "\n";

            // Single-layer fitters on SOSD for eps in {8, 16, 64}
            if (eps == 8 || eps == 16 || eps == 64) {
                const auto opt_half = alg_opt_u64(keys.data(), n, eps / 2, false);
                const std::size_t m_an = count_anchored_u64(keys.data(), n, eps);
                const std::size_t m_sc = count_shrinking_cone_u64(keys.data(), n, eps);
                const std::size_t m_rs = count_radix_spline_u64(keys.data(), n, eps);
                const std::size_t m_sw = count_native_swing_u64(keys.data(), n, eps);
                const int brk_ok = (m1 <= m_sc && m_sc <= opt_half.size()) ? 1 : 0;
                f_fit << name << "," << n << "," << eps << ","
                      << m1 << "," << m_an << "," << m_sc << "," << m_rs << "," << m_sw << ","
                      << std::fixed << std::setprecision(3)
                      << (double(m_sc) / m1) << ","
                      << (double(m_rs) / m1) << ","
                      << (double(m_sw) / m1) << ","
                      << brk_ok << "\n";
                f_fit.flush();
                std::cerr << "    [fitters eps=" << eps << "] M_opt=" << m1
                          << " M_an=" << m_an << " M_sc=" << m_sc
                          << " (" << std::setprecision(2) << (double(m_sc)/m1) << "x)"
                          << " M_rs=" << m_rs
                          << " M_swing=" << m_sw
                          << " (" << (double(m_sw)/m1) << "x) brk=" << brk_ok << "\n";
            }
        }
    }
}

}  // namespace

int main(int argc, char** argv) {
    if (argc < 2) {
        std::cerr << "Usage: sosd_bench <synthetic-fitters|swing-gaussian|sosd> [sosd_data_dir]\n";
        return 1;
    }
    const std::string cmd = argv[1];
    if (cmd == "synthetic-fitters") {
        run_synthetic_fitters();
    } else if (cmd == "swing-gaussian") {
        run_swing_gaussian();
    } else if (cmd == "sosd") {
        const std::string dir = (argc >= 3) ? argv[2] : "reproduce/sosd_data";
        run_sosd_all(dir);
    } else {
        std::cerr << "Unknown command: " << cmd << "\n";
        return 1;
    }
    return 0;
}
