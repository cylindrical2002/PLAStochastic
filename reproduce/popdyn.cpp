// popdyn.cpp -- Exact O(n) O'Rourke shrinking-cone PLA segmentation,
// EP & RE hierarchy builders, and population-dynamics evaluation
// accompanying "The Anatomy of Piecewise-Linear Learned Indexes".
//
// Build:
//   g++ -O3 -std=c++17 reproduce/popdyn.cpp -o reproduce/popdyn

#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <random>
#include <string>
#include <vector>

namespace {

constexpr double kKappaOpt = 3.53841980;
constexpr double kAlphaOpt = 0.17815941;
constexpr double kCInfCoeff = kKappaOpt / kAlphaOpt;  // ~19.860981
constexpr double kRhoStar = 0.25710;

struct Point {
    double x;
    double y;
};

// Exact O(n) shrinking-cone greedy segmentation (ALG-OPT).
// Returns the starting indices 0 = s_0 < s_1 < ... < s_{M-1} < n of the M segments.
std::vector<std::size_t> alg_opt_starts(const std::vector<double>& keys, double eps) {
    const std::size_t n = keys.size();
    assert(n >= 1 && eps >= 1.0);
    std::vector<std::size_t> starts;
    starts.reserve(n / static_cast<std::size_t>(std::max(2.0, eps * eps)) + 16);

    std::vector<Point> uh;
    std::vector<Point> lh;
    uh.reserve(256);
    lh.reserve(256);

    std::size_t s = 0;
    while (s < n) {
        starts.push_back(s);
        if (s + 1 >= n) {
            break;
        }

        uh.clear();
        lh.clear();
        uh.push_back({keys[s], eps});
        lh.push_back({keys[s], -eps});
        std::size_t uh_ptr = 0;
        std::size_t lh_ptr = 0;
        double s_min = -1e300;
        double s_max = 1e300;

        std::size_t e = s + 1;
        while (e < n) {
            const double k = static_cast<double>(e - s);
            const double xk = keys[e];
            const Point u_pt{xk, k + eps};
            const Point l_pt{xk, k - eps};

            while (uh_ptr + 1 < uh.size()) {
                const Point& p0 = uh[uh_ptr];
                const Point& p1 = uh[uh_ptr + 1];
                if ((l_pt.y - p1.y) * (xk - p0.x) >= (l_pt.y - p0.y) * (xk - p1.x)) {
                    ++uh_ptr;
                } else {
                    break;
                }
            }
            const double cand_min = (l_pt.y - uh[uh_ptr].y) / (xk - uh[uh_ptr].x);

            while (lh_ptr + 1 < lh.size()) {
                const Point& p0 = lh[lh_ptr];
                const Point& p1 = lh[lh_ptr + 1];
                if ((u_pt.y - p1.y) * (xk - p0.x) <= (u_pt.y - p0.y) * (xk - p1.x)) {
                    ++lh_ptr;
                } else {
                    break;
                }
            }
            const double cand_max = (u_pt.y - lh[lh_ptr].y) / (xk - lh[lh_ptr].x);

            const double next_min = std::max(s_min, cand_min);
            const double next_max = std::min(s_max, cand_max);
            if (next_min > next_max + 1e-13 * std::max(1.0, std::abs(next_min))) {
                break;
            }
            s_min = next_min;
            s_max = next_max;

            while (uh.size() >= 2) {
                const Point& p0 = uh[uh.size() - 2];
                const Point& p1 = uh[uh.size() - 1];
                if ((p1.y - p0.y) * (xk - p0.x) >= (u_pt.y - p0.y) * (p1.x - p0.x)) {
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
                const Point& p0 = lh[lh.size() - 2];
                const Point& p1 = lh[lh.size() - 1];
                if ((p1.y - p0.y) * (xk - p0.x) <= (l_pt.y - p0.y) * (p1.x - p0.x)) {
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
        s = e;
    }
    return starts;
}

double relative_gap_variance(const std::vector<double>& keys) {
    if (keys.size() < 3) {
        return 0.0;
    }
    const std::size_t m = keys.size() - 1;
    long double sum = 0.0;
    long double sum_sq = 0.0;
    for (std::size_t i = 0; i < m; ++i) {
        const long double g = static_cast<long double>(keys[i + 1] - keys[i]);
        sum += g;
        sum_sq += g * g;
    }
    const long double mean = sum / static_cast<long double>(m);
    const long double var = std::max<long double>(0.0L, sum_sq / static_cast<long double>(m) - mean * mean);
    return static_cast<double>(var / (mean * mean));
}

struct HierarchyStats {
    int height = 0;
    std::size_t m1 = 0;
    std::vector<std::size_t> n_layer;
    std::vector<std::size_t> m_layer;
    std::vector<double> rel_var;
};

HierarchyStats build_ep(std::vector<double> pivots, double eps, bool track_var = false) {
    HierarchyStats st;
    while (pivots.size() > 1) {
        st.n_layer.push_back(pivots.size());
        if (track_var) {
            st.rel_var.push_back(relative_gap_variance(pivots));
        }
        auto starts = alg_opt_starts(pivots, eps);
        if (st.height == 0) {
            st.m1 = starts.size();
        }
        st.m_layer.push_back(starts.size());
        std::vector<double> next_pivots;
        next_pivots.reserve(starts.size());
        for (std::size_t idx : starts) {
            next_pivots.push_back(pivots[idx]);
        }
        pivots = std::move(next_pivots);
        ++st.height;
    }
    st.n_layer.push_back(1);
    return st;
}

HierarchyStats build_re(std::vector<double> pivots, double eps, bool track_var = false) {
    HierarchyStats st;
    while (pivots.size() > 1) {
        const std::size_t n_l = pivots.size();
        st.n_layer.push_back(n_l);
        if (track_var) {
            st.rel_var.push_back(relative_gap_variance(pivots));
        }
        auto starts = alg_opt_starts(pivots, eps);
        const std::size_t m_next = starts.size();
        if (st.height == 0) {
            st.m1 = m_next;
        }
        st.m_layer.push_back(m_next);
        const std::size_t d_l = n_l / m_next;
        const std::size_t n_next = (n_l + d_l - 1) / d_l;
        std::vector<double> next_pivots;
        next_pivots.reserve(n_next);
        for (std::size_t j = 0; j < n_next; ++j) {
            next_pivots.push_back(pivots[j * d_l]);
        }
        pivots = std::move(next_pivots);
        ++st.height;
    }
    st.n_layer.push_back(1);
    return st;
}

// Generate Model G keys from i.i.d. Exp(1) or Unif[0,2] gaps.
std::vector<double> sample_model_g(std::size_t n, const std::string& family, std::uint64_t seed) {
    std::mt19937_64 rng(seed);
    std::vector<double> keys(n);
    long double acc = 0.0L;
    keys[0] = 0.0;
    if (family == "exp") {
        std::exponential_distribution<double> dist(1.0);
        for (std::size_t i = 1; i < n; ++i) {
            acc += std::max(1e-15, dist(rng));
            keys[i] = static_cast<double>(acc);
        }
    } else {
        std::uniform_real_distribution<double> dist(1e-12, 2.0);
        for (std::size_t i = 1; i < n; ++i) {
            acc += dist(rng);
            keys[i] = static_cast<double>(acc);
        }
    }
    return keys;
}

// Generate sorted Model K keys on [0,1] from f_delta(x) = 1 + delta*(2x - 1)
// via Renyi exponential spacings U_(i) = Gamma_i / Gamma_{n+1} and exact quantile Q_delta(u).
std::vector<double> sample_model_k_linear(std::size_t n, double delta, std::uint64_t seed) {
    std::mt19937_64 rng(seed);
    std::exponential_distribution<double> exp_dist(1.0);
    std::vector<double> cum(n + 1);
    long double acc = 0.0L;
    for (std::size_t i = 0; i <= n; ++i) {
        acc += std::max(1e-15, exp_dist(rng));
        cum[i] = static_cast<double>(acc);
    }
    const double total = cum[n];
    std::vector<double> keys(n);
    if (delta < 1e-12) {
        for (std::size_t i = 0; i < n; ++i) {
            keys[i] = cum[i] / total;
        }
    } else {
        const double one_minus_d = 1.0 - delta;
        const double sq = one_minus_d * one_minus_d;
        for (std::size_t i = 0; i < n; ++i) {
            const double u = cum[i] / total;
            keys[i] = (std::sqrt(sq + 4.0 * delta * u) - one_minus_d) / (2.0 * delta);
        }
    }
    return keys;
}

void run_variance_collapse() {
    std::cout << "family,mode,eps,v0,v1,v2,v3\n";
    for (const std::string fam : {"exp", "unif"}) {
        for (int eps : {4, 16}) {
            const std::size_t pop_gaps = (eps <= 4) ? 50000 : 12000;
            std::mt19937_64 rng(42 + eps);
            std::vector<double> gaps(pop_gaps);
            if (fam == "exp") {
                std::exponential_distribution<double> d(1.0);
                for (auto& g : gaps) g = std::max(1e-15, d(rng));
            } else {
                std::uniform_real_distribution<double> d(1e-12, 2.0);
                for (auto& g : gaps) g = d(rng);
            }

            std::vector<double> v_layers;
            for (int layer = 0; layer <= 3; ++layer) {
                std::vector<double> keys(gaps.size() + 1, 0.0);
                long double acc = 0.0L;
                for (std::size_t i = 0; i < gaps.size(); ++i) {
                    acc += gaps[i];
                    keys[i + 1] = static_cast<double>(acc);
                }
                v_layers.push_back(relative_gap_variance(keys));
                if (layer == 3) break;

                std::uniform_int_distribution<std::size_t> pick(0, gaps.size() - 1);
                const std::size_t stream_len =
                    static_cast<std::size_t>((pop_gaps + 10) * kCInfCoeff * eps * eps * 1.15);
                std::vector<double> stream_keys(stream_len + 1, 0.0);
                long double b_acc = 0.0L;
                for (std::size_t i = 0; i < stream_len; ++i) {
                    b_acc += gaps[pick(rng)];
                    stream_keys[i + 1] = static_cast<double>(b_acc);
                }
                auto starts = alg_opt_starts(stream_keys, static_cast<double>(eps));
                std::vector<double> next_gaps;
                next_gaps.reserve(starts.size());
                // Skip j = 0 transient segment and trailing boundary segment.
                for (std::size_t j = 1; j + 2 < starts.size(); ++j) {
                    next_gaps.push_back(stream_keys[starts[j + 1]] - stream_keys[starts[j]]);
                }
                double mean = std::accumulate(next_gaps.begin(), next_gaps.end(), 0.0) / next_gaps.size();
                for (auto& g : next_gaps) g /= mean;
                gaps = std::move(next_gaps);
            }
            std::cout << std::fixed << std::setprecision(4)
                      << fam << ",EP," << eps << ","
                      << v_layers[0] << "," << v_layers[1] << ","
                      << v_layers[2] << "," << v_layers[3] << "\n";
        }
    }
}

void run_fanout_scaling() {
    std::cout << "eps,C_hat_over_C_inf,shifted_square,abs_residual\n";
    for (int eps : {2, 4, 8, 16, 32, 64}) {
        const double c_inf = kCInfCoeff * eps * eps;
        const std::size_t target_segs =
            std::min<std::size_t>(40000, std::max<std::size_t>(1200, static_cast<std::size_t>(25000000.0 / c_inf)));
        std::mt19937_64 rng(1000 + eps);
        std::exponential_distribution<double> exp_d(1.0);
        std::vector<double> gaps(target_segs);
        for (auto& g : gaps) g = std::max(1e-15, exp_d(rng));

        double c_hat = 0.0;
        for (int iter = 0; iter < 3; ++iter) {
            std::uniform_int_distribution<std::size_t> pick(0, gaps.size() - 1);
            const std::size_t stream_len =
                static_cast<std::size_t>((target_segs + 8) * c_inf * (1.0 + 0.6 / eps));
            std::vector<double> stream_keys(stream_len + 1, 0.0);
            long double b_acc = 0.0L;
            for (std::size_t i = 0; i < stream_len; ++i) {
                b_acc += gaps[pick(rng)];
                stream_keys[i + 1] = static_cast<double>(b_acc);
            }
            auto starts = alg_opt_starts(stream_keys, static_cast<double>(eps));
            assert(starts.size() > 4);
            // Measure interior stationary segments j = 1 .. starts.size() - 3.
            const std::size_t total_keys = starts[starts.size() - 1] - starts[1];
            const std::size_t total_segs = starts.size() - 2;
            c_hat = static_cast<double>(total_keys) / static_cast<double>(total_segs);

            std::vector<double> next_gaps;
            next_gaps.reserve(total_segs);
            for (std::size_t j = 1; j + 2 < starts.size(); ++j) {
                next_gaps.push_back(stream_keys[starts[j + 1]] - stream_keys[starts[j]]);
            }
            double mean = std::accumulate(next_gaps.begin(), next_gaps.end(), 0.0) / next_gaps.size();
            for (auto& g : next_gaps) g /= mean;
            gaps = std::move(next_gaps);
        }
        const double ratio = c_hat / c_inf;
        const double pred = (1.0 + kRhoStar / eps) * (1.0 + kRhoStar / eps);
        std::cout << std::fixed << std::setprecision(4)
                  << eps << "," << ratio << "," << pred << "," << std::abs(ratio - pred) << "\n";
    }
}

void run_trajectory(std::size_t n) {
    std::cout << "mode,delta,height,layers\n";
    {
        auto keys = sample_model_k_linear(n, 0.0, 2026);
        auto ep = build_ep(keys, 4.0);
        auto re = build_re(std::move(keys), 4.0);
        std::cout << "EP,0.0," << ep.height << ",";
        for (std::size_t i = 0; i < ep.n_layer.size(); ++i) {
            if (i) std::cout << "->";
            std::cout << ep.n_layer[i];
        }
        std::cout << "\nRE,0.0," << re.height << ",";
        for (std::size_t i = 0; i < re.n_layer.size(); ++i) {
            if (i) std::cout << "->";
            std::cout << re.n_layer[i];
        }
        std::cout << "\n";
    }
    {
        auto keys = sample_model_k_linear(n, 0.8, 2026);
        auto re = build_re(std::move(keys), 4.0);
        std::cout << "RE,0.8," << re.height << ",";
        for (std::size_t i = 0; i < re.n_layer.size(); ++i) {
            if (i) std::cout << "->";
            std::cout << re.n_layer[i];
        }
        std::cout << "\n";
    }
}

void run_delta_scan(std::size_t n) {
    const std::vector<double> deltas = {1e-5, 3e-5, 1e-4, 3e-4, 1e-3, 3e-3, 1e-2, 3e-2, 1e-1, 3e-1, 8e-1};
    std::cout << "delta,eps,mode,height,M2\n";
    for (double delta : deltas) {
        auto keys = sample_model_k_linear(n, delta, 2026);
        for (int eps : {2, 4, 8, 16}) {
            auto re = build_re(keys, static_cast<double>(eps));
            const std::size_t m2 = re.m_layer.size() >= 2 ? re.m_layer[1] : 1;
            std::cout << delta << "," << eps << ",RE," << re.height << "," << m2 << "\n";
        }
    }
}

}  // namespace

int main(int argc, char** argv) {
    if (argc < 2) {
        std::cerr << "Usage: popdyn <variance|fanout|trajectory|delta-scan|eval-run> [args...]\n";
        return 1;
    }
    const std::string cmd = argv[1];
    if (cmd == "variance") {
        run_variance_collapse();
    } else if (cmd == "fanout") {
        run_fanout_scaling();
    } else if (cmd == "trajectory") {
        const std::size_t n = (argc >= 3) ? std::stoull(argv[2]) : 100000000ULL;
        run_trajectory(n);
    } else if (cmd == "delta-scan") {
        const std::size_t n = (argc >= 3) ? std::stoull(argv[2]) : 10000000ULL;
        run_delta_scan(n);
    } else if (cmd == "eval-run") {
        if (argc < 7) {
            std::cerr << "Usage: popdyn eval-run <EP|RE> <exp|unif|linear08> <n> <eps> <seed>\n";
            return 1;
        }
        const std::string mode = argv[2];
        const std::string fam = argv[3];
        const std::size_t n = std::stoull(argv[4]);
        const double eps = std::stod(argv[5]);
        const std::uint64_t seed = std::stoull(argv[6]);
        std::vector<double> keys = (fam == "linear08")
                                       ? sample_model_k_linear(n, 0.8, seed)
                                       : sample_model_g(n, fam, seed);
        HierarchyStats st = (mode == "EP") ? build_ep(std::move(keys), eps)
                                           : build_re(std::move(keys), eps);
        const std::size_t n_penult = st.n_layer.size() >= 2 ? st.n_layer[st.n_layer.size() - 2] : 1;
        std::cout << st.height << " " << st.m1 << " " << n_penult << "\n";
    } else {
        std::cerr << "Unknown subcommand: " << cmd << "\n";
        return 1;
    }
    return 0;
}
