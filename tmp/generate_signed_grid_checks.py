from pathlib import Path
root = Path(__file__).resolve().parents[1]
parts = 4
blocks_per_part = 173
for part in range(parts):
    low = part * blocks_per_part * 256
    high = min(177147, low + blocks_per_part * 256)
    lines = ['import Problems.Collatz.PreimageWeights12', '',
             f'namespace Problems.Collatz.PreimageCheck12Part{part}',
             'open PreimageWeights12',
             'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '']
    for j in range(blocks_per_part):
        offset = low + 256*j
        lines += [f'private theorem chunk{j} : ∀ n < 256, {offset} + n < 177147 →',
                  f'    row ({offset} + n) := by decide +kernel', '']
    lines += [f'theorem checked : ∀ i, {low} ≤ i → i < {high} → row i := by',
              f'  have hc : ∀ j < {blocks_per_part}, ∀ n < 256,',
              f'      {low} + 256*j + n < 177147 → row ({low} + 256*j + n) := by',
              '    intro j hj', '    interval_cases j']
    lines += [f'    · exact chunk{j}' for j in range(blocks_per_part)]
    lines += ['  intro i hlo hhi',
              f'  have h := hc ((i-{low})/256) (by omega) ((i-{low})%256) (by omega) (by omega)',
              f'  have he : {low} + 256*((i-{low})/256) + (i-{low})%256 = i := by omega',
              '  simpa only [he] using h', '',
              f'end Problems.Collatz.PreimageCheck12Part{part}', '']
    (root/f'formal/Problems/Collatz/PreimageCheck12Part{part}.lean').write_text('\n'.join(lines), encoding='utf-8')

lines = [f'import Problems.Collatz.PreimageCheck12Part{j}' for j in range(parts)]
lines += ['import Problems.Collatz.PreimageCertificate', '',
          'namespace Problems.Collatz.PreimageCertificate12',
          'open PreimageWeights12 PreimageGrowth PreimageCertificate', '',
          'theorem all_rows : ∀ i < 177147, row i := by',
          '  intro i hi',
          '  by_cases h0 : i < 44288',
          '  · exact PreimageCheck12Part0.checked i (by omega) h0',
          '  by_cases h1 : i < 88576',
          '  · exact PreimageCheck12Part1.checked i (by omega) h1',
          '  by_cases h2 : i < 132864',
          '  · exact PreimageCheck12Part2.checked i (by omega) h2',
          '  exact PreimageCheck12Part3.checked i (by omega) hi', '',
          'theorem weight_system : WeightSystem 5059 5000 1000000000000',
          '    (fun a => c (a % 531441)) :=',
          '  weightSystem_of_rows c all_rows', '',
          'theorem target_growth {a : ℕ} (ha : 0 < a) (ha3 : a % 3 ≠ 0) :',
          '    ∃ r X₀, 4096 ≤ r ∧ 1 ≤ c (r % 531441) ∧ ∀ t, X₀ ≤ PreimageGrid.cap t * r →',
          '      c (r % 531441) * 5059^t * 5000^100 ≤',
          '        PreimageGrid.count a (PreimageGrid.cap t * r) *',
          '          (1000000000000 * 5000^t * 5059^100) :=',
          '  growth_for_target (by norm_num) (by norm_num) weight_system ha ha3', '',
          'end Problems.Collatz.PreimageCertificate12', '']
(root/'formal/Problems/Collatz/PreimageCertificate12.lean').write_text('\n'.join(lines),encoding='utf-8')
print('Generated four certificate-check modules and the target-growth assembly.')
