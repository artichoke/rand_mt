#!/usr/bin/env ruby
# frozen_string_literal: true

Random.srand 33
floats_a = 20.times.map { Random.rand }

Random.srand 33
floats_b = 20.times.map { Random.rand }

raise 'not reproducible' unless floats_a == floats_b

puts floats_a
