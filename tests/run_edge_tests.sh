#!/usr/bin/env bash
set -e

SPIN_BIN="../Src/spin"
TEST_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$TEST_DIR"

if [ ! -f "$SPIN_BIN" ]; then
    echo "Building spin..."
    (cd ../Src && make)
fi

echo "=========================================="
echo " Running Spin Edge Case Test Suite"
echo "=========================================="

FAILED=0

run_test() {
    local name="$1"
    local pml="$2"
    local expect_error="$3" # 0 for success, 1 for error expected

    echo -n "Testing $name ... "

    # Clean previous verifier files
    rm -f pan pan.*

    # Generate verifier
    "$SPIN_BIN" -a "$pml" > /dev/null 2>&1
    gcc -O2 -o pan pan.c > /dev/null 2>&1

    # Run verifier
    local output
    output=$(./pan 2>&1 || true)

    local errors
    errors=$(echo "$output" | grep -E "errors: [0-9]+" | head -n1 | awk -F'errors: ' '{print $2}' | awk '{print $1}')

    rm -f pan pan.* "$pml.trail"

    if [ "$expect_error" -eq 1 ]; then
        if [ "$errors" -gt 0 ]; then
            echo "PASSED (Detected expected error count: $errors)"
        else
            echo "FAILED (Expected errors but got 0)"
            FAILED=$((FAILED + 1))
        fi
    else
        if [ "$errors" -eq 0 ]; then
            echo "PASSED (0 errors as expected)"
        else
            echo "FAILED (Expected 0 errors but got $errors)"
            FAILED=$((FAILED + 1))
        fi
    fi
}

# 1. Minimal model (expect 0 errors)
run_test "Minimal Model" "edge_minimal.pml" 0

# 2. Deadlock model (expect >0 errors)
run_test "Deadlock Detection" "edge_deadlock.pml" 1

# 3. Assert failure model (expect >0 errors)
run_test "Assertion Failure Detection" "edge_assert_fail.pml" 1

# 4. Array bounds model (expect 0 errors)
run_test "Array Access & Operations" "edge_array_bounds.pml" 0

# 5. Division operation (expect 0 errors)
run_test "Division & Math Operations" "edge_div_zero.pml" 0

echo "=========================================="
if [ "$FAILED" -eq 0 ]; then
    echo " ALL EDGE CASE TESTS PASSED SUCCESSFULLY!"
    exit 0
else
    echo " $FAILED TEST(S) FAILED!"
    exit 1
fi
