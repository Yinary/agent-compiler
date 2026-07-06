# ToyC Compiler

ToyC语言编译器，目标代码为RISC-V32汇编。

## 构建

```bash
dune build
```

## 使用

```bash
./_build/default/bin/main.exe < input.tc > output.s
```

## 测试

```bash
./test.sh
```

## 运行生成的汇编

```bash
riscv64-unknown-elf-as -march=rv32im -mabi=ilp32 -o program.o program.s
riscv64-unknown-elf-ld -m elf32lriscv -o program start.o program.o
qemu-riscv32 ./program
echo $?
```
