#!/bin/bash

# Simple test script for ToyC compiler

set -e

COMPILER="_build/default/bin/main.exe"

# Build the compiler
echo "Building compiler..."
dune build 2>/dev/null

# Create runtime
cat > /tmp/start.s << 'EOF'
.section .text
.globl _start
_start:
    la sp, _stack_top
    call main
    li a7, 93
    ecall

.section .bss
.align 4
_stack:
    .space 65536
_stack_top:
EOF

riscv64-unknown-elf-as -march=rv32im -mabi=ilp32 -o /tmp/start.o /tmp/start.s

# Function to test a ToyC program
test_program() {
    local test_file=$1
    local expected=$2
    local description=$3
    
    echo -n "Testing $description... "
    
    # Compile ToyC to RISC-V assembly
    $COMPILER < "$test_file" > /tmp/test.s
    
    # Assemble and link
    riscv64-unknown-elf-as -march=rv32im -mabi=ilp32 -o /tmp/test.o /tmp/test.s
    riscv64-unknown-elf-ld -m elf32lriscv -o /tmp/test /tmp/start.o /tmp/test.o
    
    # Run and check exit code
    result=$(qemu-riscv32 /tmp/test; echo $?)
    
    if [ "$result" -eq "$expected" ]; then
        echo "PASS"
    else
        echo "FAIL (expected $expected, got $result)"
        exit 1
    fi
}

# Run tests
echo ""
echo "Running tests..."
echo "================"

# Test 1: Simple return
cat > /tmp/test1.tc << 'EOF'
int main() {
    return 42;
}
EOF
test_program /tmp/test1.tc 42 "Simple return"

# Test 2: Variables and arithmetic
cat > /tmp/test2.tc << 'EOF'
int main() {
    int x = 10;
    int y = 20;
    int z = x + y;
    return z;
}
EOF
test_program /tmp/test2.tc 30 "Variables and arithmetic"

# Test 3: Function calls
cat > /tmp/test3.tc << 'EOF'
int add(int a, int b) {
    return a + b;
}

int main() {
    int x = 10;
    int y = 20;
    int z = add(x, y);
    return z;
}
EOF
test_program /tmp/test3.tc 30 "Function calls"

# Test 4: If-else
cat > /tmp/test4.tc << 'EOF'
int main() {
    int x = 10;
    if (x > 5) {
        return 1;
    } else {
        return 0;
    }
}
EOF
test_program /tmp/test4.tc 1 "If-else"

# Test 5: While loop
cat > /tmp/test5.tc << 'EOF'
int main() {
    int sum = 0;
    int i = 1;
    while (i <= 10) {
        sum = sum + i;
        i = i + 1;
    }
    return sum;
}
EOF
test_program /tmp/test5.tc 55 "While loop"

# Test 6: Break and continue
cat > /tmp/test6.tc << 'EOF'
int main() {
    int sum = 0;
    int i = 0;
    while (i < 100) {
        i = i + 1;
        if (i % 2 == 0) {
            continue;
        }
        if (i > 10) {
            break;
        }
        sum = sum + i;
    }
    return sum;
}
EOF
test_program /tmp/test6.tc 25 "Break and continue"

# Test 7: Recursion
cat > /tmp/test7.tc << 'EOF'
int factorial(int n) {
    if (n <= 1) {
        return 1;
    }
    return n * factorial(n - 1);
}

int main() {
    return factorial(5);
}
EOF
test_program /tmp/test7.tc 120 "Recursion"

# Test 8: Global variables
cat > /tmp/test8.tc << 'EOF'
int global_var = 42;

int main() {
    return global_var;
}
EOF
test_program /tmp/test8.tc 42 "Global variables"

# Test 9: Constants
cat > /tmp/test9.tc << 'EOF'
const int MAX = 100;

int main() {
    const int LOCAL = 10;
    return MAX + LOCAL;
}
EOF
test_program /tmp/test9.tc 110 "Constants"

# Test 10: Fibonacci
cat > /tmp/test10.tc << 'EOF'
int fibonacci(int n) {
    if (n <= 1) {
        return n;
    }
    return fibonacci(n - 1) + fibonacci(n - 2);
}

int main() {
    return fibonacci(10);
}
EOF
test_program /tmp/test10.tc 55 "Fibonacci"

echo ""
echo "All tests passed!"
