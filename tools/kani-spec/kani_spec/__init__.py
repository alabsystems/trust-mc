# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Deterministic generator for the Kani functional spec (spec/kani/<rev>/)."""

GENERATOR_VERSION = "kani-spec/1.0.0"
SPEC_REVISION = 1


class SpecError(Exception):
    """A fail-closed refusal: the inputs do not match the pins or the overlay."""
