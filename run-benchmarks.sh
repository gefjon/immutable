#!/usr/bin/env bash

sbcl --dynamic-space-size 4096 \
     --disable-debugger \
     --eval '(ql:quickload "immutable/benchmark/compare-batch-inserts")' \
     --eval '(immutable/benchmark/compare-batch-inserts:run-benchmarks)' \
     --eval '(sb-ext:exit :code 0)'
