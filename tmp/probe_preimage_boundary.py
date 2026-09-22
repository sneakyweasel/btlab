import json
from research.juggler_sequence.negative_preimage_density import g_minus, negative_cycle_members

seeds = {0, 1, 5, 17}
cycle = negative_cycle_members() | {0}
all_states = set(cycle)
max_steps = (0, 0)
max_height = (0, 0)
for start in range(4096):
    n, steps = start, 0
    seen = set()
    while n not in seeds:
        assert n not in seen, (start, n)
        seen.add(n)
        if n > max_height[1]:
            max_height = (start, n)
        n = g_minus(n)
        steps += 1
    all_states.update(seen)
    max_steps = max(max_steps, (steps, start))
print(json.dumps({
    'max_steps_to_seed': max_steps,
    'max_height': max_height,
    'closed_union_size': len(all_states),
    'extras_above_4095': sum(n >= 4096 for n in all_states),
    'closed': all(g_minus(n) in all_states for n in all_states),
    'power_of_two_strict_bound': max(all_states).bit_length(),
}, indent=2))
