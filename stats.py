#!/usr/bin/env python3
# File:  stats.py
# Author:  mikolas
# Created on:  Thu Feb 13 16:34:01 CET 2025
# Copyright (C) 2025, Mikolas Janota


class Stat:
    def __init__(self, descr, val=0):
        self.descr = descr
        self.val = val

    def set_val(self, i):
        self.val = i

    def inc(self, i=1):
        self.val += i

    def update_max(self, v):
        self.val = v if self.val < v else self.val


class Stats:
    def __init__(self):
        self.all_stats = []
        self.st_rounds = self.mkStat("simple-terms rounds")
        self.nice_insts = self.mkStat("number of nice instantiations")
        self.new_facts = self.mkStat("number of new facts")

    def mkStat(self, descr):
        rv = Stat(descr)
        self.all_stats.append(rv)
        return rv

    def all(self):
        return self.all_stats
