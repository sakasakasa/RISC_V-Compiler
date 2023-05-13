# Compiler

## Setup

```
git clone https://github.com/cpuex-19-6/Compiler.git
cd Compiler
make
```

## Usage

例えば、`test/` ディレクトリ内の `float-check.ml`をコンパイルする場合は、
```
make test/float-check.s
```
で`test/` ディレクトリ内の `float-check.ml` のアセンブラ `float-check.s` が出力されます。  





レイトレをコンパイルしたい場合は、

```
make min-rt
```
で `raytrace.s` にアセンブラが出力されます。