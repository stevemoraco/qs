// Exhaustive small-instance audit for the 4-variable marker gadget.
//
// The target is 1 exactly at Hamming weights 1 and 4.  We enumerate acyclic
// full-binary-basis circuits by the set of signals computed so far, quotienting
// by three sound symmetries for this symmetric target:
//
//   * independent signal complementation (absorbed into arbitrary 2-input gate
//     truth tables),
//   * permutation of the four input variables,
//   * ordering/duplication of already available signals.
//
// Constants, unary gates, unused gates, duplicate signals, and complementary
// duplicate signals cannot occur in a minimum circuit in the full B_2 basis,
// so they are omitted.  The companion note audits these reductions.  This is
// an exhaustive finite computation, not a formal proof and not P versus NP.

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <unordered_set>
#include <vector>

using Truth = std::uint16_t;

struct VectorHash {
  std::size_t operator()(const std::vector<Truth>& values) const noexcept {
    std::uint64_t hash = 1469598103934665603ULL;
    for (Truth value : values) {
      hash ^= value;
      hash *= 1099511628211ULL;
    }
    return static_cast<std::size_t>(hash);
  }
};

std::vector<std::array<int, 4>> input_permutations;
Truth inputs[4];

Truth canonical_complement(Truth value) {
  const Truth complement = static_cast<Truth>(~value);
  return std::min(value, complement);
}

Truth permute_truth_table(Truth function, int permutation_index) {
  Truth result = 0;
  const auto permutation = input_permutations[permutation_index];
  for (int assignment = 0; assignment < 16; ++assignment) {
    int permuted_assignment = 0;
    for (int input = 0; input < 4; ++input) {
      if ((assignment >> input) & 1) {
        permuted_assignment |= 1 << permutation[input];
      }
    }
    if ((function >> permuted_assignment) & 1) {
      result |= static_cast<Truth>(1U << assignment);
    }
  }
  return result;
}

std::vector<Truth> canonical_state(std::vector<Truth> state) {
  std::vector<Truth> best;
  bool first = true;
  for (int permutation = 0;
       permutation < static_cast<int>(input_permutations.size());
       ++permutation) {
    std::vector<Truth> transformed;
    transformed.reserve(state.size());
    for (Truth function : state) {
      transformed.push_back(canonical_complement(
          permute_truth_table(function, permutation)));
    }
    std::sort(transformed.begin(), transformed.end());
    if (first || transformed < best) {
      best = std::move(transformed);
      first = false;
    }
  }
  return best;
}

bool depends_on_both_inputs(int gate_truth_table) {
  int output[4];
  for (int assignment = 0; assignment < 4; ++assignment) {
    output[assignment] = (gate_truth_table >> assignment) & 1;
  }
  const bool depends_on_first =
      output[0] != output[2] || output[1] != output[3];
  const bool depends_on_second =
      output[0] != output[1] || output[2] != output[3];
  return depends_on_first && depends_on_second;
}

Truth combine(Truth first, Truth second, int gate_truth_table) {
  const Truth not_first = static_cast<Truth>(~first);
  const Truth not_second = static_cast<Truth>(~second);
  const Truth minterms[4] = {
      static_cast<Truth>(not_first & not_second),
      static_cast<Truth>(not_first & second),
      static_cast<Truth>(first & not_second),
      static_cast<Truth>(first & second),
  };
  Truth result = 0;
  for (int assignment = 0; assignment < 4; ++assignment) {
    if ((gate_truth_table >> assignment) & 1) {
      result |= minterms[assignment];
    }
  }
  return canonical_complement(result);
}

int main(int argc, char** argv) {
  const int maximum_gates = argc > 1 ? std::atoi(argv[1]) : 6;

  std::array<int, 4> permutation = {0, 1, 2, 3};
  do {
    input_permutations.push_back(permutation);
  } while (std::next_permutation(permutation.begin(), permutation.end()));

  for (int input = 0; input < 4; ++input) {
    Truth function = 0;
    for (int assignment = 0; assignment < 16; ++assignment) {
      if ((assignment >> input) & 1) {
        function |= static_cast<Truth>(1U << assignment);
      }
    }
    inputs[input] = canonical_complement(function);
  }

  Truth target = 0;
  for (int assignment = 0; assignment < 16; ++assignment) {
    const int weight = __builtin_popcount(static_cast<unsigned>(assignment));
    if (weight == 1 || weight == 4) {
      target |= static_cast<Truth>(1U << assignment);
    }
  }
  target = canonical_complement(target);
  std::cerr << "target 0x" << std::hex << target << std::dec << '\n';

  std::vector<int> operations;
  for (int truth_table = 0; truth_table < 16; ++truth_table) {
    if (depends_on_both_inputs(truth_table)) {
      operations.push_back(truth_table);
    }
  }

  std::unordered_set<std::vector<Truth>, VectorHash> current;
  std::unordered_set<std::vector<Truth>, VectorHash> next;
  current.insert(std::vector<Truth>{});

  for (int depth = 0; depth < maximum_gates; ++depth) {
    next.clear();
    std::size_t generated = 0;

    for (const auto& state : current) {
      std::vector<Truth> available(inputs, inputs + 4);
      available.insert(available.end(), state.begin(), state.end());
      std::sort(available.begin(), available.end());
      available.erase(std::unique(available.begin(), available.end()),
                      available.end());

      const int count = static_cast<int>(available.size());
      for (int first = 0; first < count; ++first) {
        for (int second = first + 1; second < count; ++second) {
          for (int operation : operations) {
            const Truth output =
                combine(available[first], available[second], operation);
            ++generated;

            if (output == target) {
              std::cout << "FOUND depth " << depth + 1 << '\n';
              return 0;
            }

            if (depth == maximum_gates - 1 || output == 0 ||
                std::binary_search(available.begin(), available.end(), output)) {
              continue;
            }

            std::vector<Truth> successor = state;
            successor.push_back(output);
            std::sort(successor.begin(), successor.end());
            successor = canonical_state(std::move(successor));
            next.insert(std::move(successor));
          }
        }
      }
    }

    std::cerr << "depth " << depth + 1 << " states " << next.size()
              << " generated " << generated << '\n';
    current.swap(next);
  }

  std::cout << "NOTFOUND up to " << maximum_gates << '\n';
  return 0;
}
