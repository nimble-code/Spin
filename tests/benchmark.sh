#!/usr/bin/env bash
set -e

SPIN_BIN="../Src/spin"
TEST_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$TEST_DIR"

echo "=========================================="
echo "      Spin Execution Speed Benchmark      "
echo "=========================================="

run_bench() {
    local name="$1"
    local pml="$2"

    echo "--- Benchmarking model: $name ($pml) ---"
    
    # 1. Measure Spin AST parse & verifier code generation time
    local start_parse=$(python3 -c "import time; print(time.time())")
    for i in {1..50}; do
        "$SPIN_BIN" -a "$pml" > /dev/null 2>&1
    done
    local end_parse=$(python3 -c "import time; print(time.time())")
    local parse_time=$(python3 -c "print(f'{($end_parse - $start_parse)/50:.6f}')")
    echo "  Average Parse & Gen Time (50 runs): ${parse_time}s"

    # 2. Compile verifier pan.c
    gcc -O3 -o pan pan.c > /dev/null 2>&1

    # 3. Measure pan verifier state space exploration throughput
    local start_sim=$(python3 -c "import time; print(time.time())")
    local pan_output=$(./pan 2>&1 || true)
    local end_sim=$(python3 -c "import time; print(time.time())")
    local sim_time=$(python3 -c "print(f'{($end_sim - $start_sim):.6f}')")

    local states=$(echo "$pan_output" | grep -E "states, stored" | head -n1 | awk '{print $1}')
    local transitions=$(echo "$pan_output" | grep -E "transitions" | head -n1 | awk '{print $1}')
    
    echo "  State Search Time: ${sim_time}s"
    if [ -n "$states" ] && [ "$states" -gt 0 ]; then
        local sps=$(python3 -c "print(f'{int($states / max($sim_time, 0.000001)):,}')")
        echo "  States Explored: $states ($sps states/sec)"
    fi
    if [ -n "$transitions" ]; then
        echo "  Transitions Evaluated: $transitions"
    fi
    rm -f pan pan.* "$pml.trail"
    echo ""
}

run_bench "Leader Election (leader0.pml)" "../Examples/leader0.pml"
run_bench "Peterson Mutex (peterson.pml)" "../Examples/peterson.pml"
run_bench "Pathfinder Protocol (pathfinder.pml)" "../Examples/pathfinder.pml"
run_bench "Eratosthenes Sieve (eratosthenes.pml)" "../Examples/eratosthenes.pml"

echo "=========================================="
echo "           Benchmark Completed            "
echo "=========================================="
