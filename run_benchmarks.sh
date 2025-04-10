#!/usr/bin/env bash

ls benchmarks/*.cnf | parallel kissat {} ">" {.}.cert
