#!/usr/bin/env sh

sbcl --dynamic-space-size 4096 \
     --disable-debugger \
     --eval '(ql:quickload "immutable/benchmark")' \
     --eval '(immutable/benchmark/main:run-benchmarks)' \
     --eval '(sb-ext:exit :code 0)'
