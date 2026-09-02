# Juggler survivor rounding-phase distribution

Status: **SURVIVOR_PHASE_CLOSED**

Scale-matched u_O / u_E census on long AboveAnchor survivors.
Not a halt theorem. A histogram is not a theorem.
Absence is NOT_OBSERVED_WITHIN_BOUND.

## Branch budget

```text
Mathematical target     exceptional rounding phase among long AA survivors
Novelty hypothesis      long survival needs near-power alignment
Maximum Phase-0 scope   streamed histograms; S-bins; hold-out; no Lean
```

## Metadata

- classification: **SURVIVOR_PHASE_CLOSED**
- n_max: `20000000` hold_split: `10000000`
- starts: `9999999` bit_cap: `142234` horizon: `477` s_max: `80`
- S counts: `{'ordinary': 5000067, 'mid': 3516206, 'long': 1341492}`
- long vs ctrl D_odd: `0.0090` D_even: `0.0059`
- long vs ordinary D_odd: `0.0057`
- train vs hold long: `0.0014`
- lag-1 indep D long/ordinary: `0.0002` / `0.0002`
- edge long/ordinary/ctrl: `0.1012` / `0.1017` / `0.1023`
- small-d long/ordinary/ctrl: `0.000148` / `0.000000` / `0.001121`
- fills unit interval: `True`

long-AA u_O / u_E histograms match scale-matched generic integers and ordinary survivors; lag-1 independence gap is not larger for long survivors; the unit interval stays occupied; already localDefect.

## Laboratories

- `37`: S=`15` min_u=`0.0` max_u=`0.9667846412096931` min_d_odd=`0`
- `69`: S=`7` min_u=`0.05068622548202478` max_u=`0.5517241379310345` min_d_odd=`180`
- `89`: S=`8` min_u=`0.051743647772862875` max_u=`0.8906752411575563` min_d_odd=`875`
- `365`: S=`15` min_u=`0.011784730434544845` max_u=`0.9328841545870797` min_d_odd=`1724`
- `501`: S=`23` min_u=`0.0` max_u=`0.9328841545870797` min_d_odd=`0`
- `1517`: S=`16` min_u=`0.037640740566259955` max_u=`0.9997968253862154` min_d_odd=`18188`
- `6187`: S=`13` min_u=`0.14017739555153164` max_u=`0.9258785049713639` min_d_odd=`838794`
- `329`: S=`23` min_u=`0.024973450386664337` max_u=`0.9474828975390511` min_d_odd=`6200`
- `33391`: S=`39` min_u=`0.048778610967171815` max_u=`0.9997275824798865` min_d_odd=`4632100`

## D statistics

- `{'long_vs_ctrl_odd': 0.009008843878729744, 'long_vs_ctrl_even': 0.005899644209069299, 'long_vs_ordinary_odd': 0.005745019296994891, 'long_vs_ordinary_even': 0.0006109301404305656, 'mid_vs_ordinary_odd': 0.004499997330474681, 'train_vs_hold_long': 0.001387209493532049, 'train_vs_ctrl': 0.008714813056433901, 'hold_vs_ctrl': 0.009681569574995774, 'max': 0.009008843878729744}`

## Existing Lean (unchanged)

- `localDefectOdd`: `True`
- `localDefectEven`: `True`
- `localDefectOdd_lt_succ`: `True`
- `AboveAnchor`: `True`
- `EnvelopeState`: `True`
- new Lean file: `False`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- histogram_is_theorem: `False`
- pvalue_is_theorem: `False`
- density_theorem: `False`
- floor_phase_lean: `False`
- excursion_reopen: `False`
- defect_cut_reopen: `False`
- itinerary_language_reopen: `False`
- global_non_realizability: `False`

## Decision

**SURVIVOR_PHASE_CLOSED**

long-AA u_O / u_E histograms match scale-matched generic integers and ordinary survivors; lag-1 independence gap is not larger for long survivors; the unit interval stays occupied; already localDefect.

