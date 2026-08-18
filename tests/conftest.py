# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Pytest configuration for the published Trust-MC regression suite.

The private-template fixture modules were intentionally removed when Trust-MC
was prepared for publication.  The surviving public tests are self-contained,
so importing or registering those removed plugins prevents collection without
providing any fixture they consume.
"""
