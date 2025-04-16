#!/usr/bin/env bash

ls benchmarks/*.cnf.gz | parallel kissat {} ">" {.}.cert
