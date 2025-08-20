#!/bin/bash

# This script builds the project's Lean code.

set -o pipefail # stop if any command fails

cd analysis/
lake exe cache get
lake build