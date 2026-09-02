# Juggler length-8 cycle-word census

Status: **LENGTH_EIGHT_CENSUS_GREEN**

Laboratory assembly of named filters. Not Paper A. Not a halt
theorem. Length nine is open.

## Inventory

- `OOOOOOOE` filter=`odd_run`
- `OOOOOOEE` filter=`two_even_ee`
- `OOOOOEOE` filter=`two_even_eoe`
- `OOOOEOOE` filter=`bootstrap_oo_suffix_threshold`
- `OOOEOOOE` filter=`bootstrap_ooo_suffix_threshold`
- `OOEOOOOE` filter=`bootstrap_odd_run_suffix_threshold`
- `OEOOOOOE` filter=`cycleMin_not_odd_even`
- `EOOOOOOE` filter=`rotate_start_even`

## Lean

- `no_cycle_itinerary_length_le_eight`: `True`
- `no_cycle_itinerary_ooooeooe`: `True`
- paper A length eight open: `True`
- no `no_cycle_itinerary_length_eight`: `True`

## Decision

**LENGTH_EIGHT_CENSUS_GREEN**

no_cycle_itinerary_length_le_eight assembles the named length-8 filters; Paper A census file still stops at seven.

