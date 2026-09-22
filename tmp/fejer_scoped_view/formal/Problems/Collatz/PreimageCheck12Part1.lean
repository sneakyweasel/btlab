import Problems.Collatz.PreimageWeights12

namespace Problems.Collatz.PreimageCheck12Part1
open PreimageWeights12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem chunk0 : ∀ n < 256, 44288 + n < 177147 →
    row (44288 + n) := by decide +kernel

private theorem chunk1 : ∀ n < 256, 44544 + n < 177147 →
    row (44544 + n) := by decide +kernel

private theorem chunk2 : ∀ n < 256, 44800 + n < 177147 →
    row (44800 + n) := by decide +kernel

private theorem chunk3 : ∀ n < 256, 45056 + n < 177147 →
    row (45056 + n) := by decide +kernel

private theorem chunk4 : ∀ n < 256, 45312 + n < 177147 →
    row (45312 + n) := by decide +kernel

private theorem chunk5 : ∀ n < 256, 45568 + n < 177147 →
    row (45568 + n) := by decide +kernel

private theorem chunk6 : ∀ n < 256, 45824 + n < 177147 →
    row (45824 + n) := by decide +kernel

private theorem chunk7 : ∀ n < 256, 46080 + n < 177147 →
    row (46080 + n) := by decide +kernel

private theorem chunk8 : ∀ n < 256, 46336 + n < 177147 →
    row (46336 + n) := by decide +kernel

private theorem chunk9 : ∀ n < 256, 46592 + n < 177147 →
    row (46592 + n) := by decide +kernel

private theorem chunk10 : ∀ n < 256, 46848 + n < 177147 →
    row (46848 + n) := by decide +kernel

private theorem chunk11 : ∀ n < 256, 47104 + n < 177147 →
    row (47104 + n) := by decide +kernel

private theorem chunk12 : ∀ n < 256, 47360 + n < 177147 →
    row (47360 + n) := by decide +kernel

private theorem chunk13 : ∀ n < 256, 47616 + n < 177147 →
    row (47616 + n) := by decide +kernel

private theorem chunk14 : ∀ n < 256, 47872 + n < 177147 →
    row (47872 + n) := by decide +kernel

private theorem chunk15 : ∀ n < 256, 48128 + n < 177147 →
    row (48128 + n) := by decide +kernel

private theorem chunk16 : ∀ n < 256, 48384 + n < 177147 →
    row (48384 + n) := by decide +kernel

private theorem chunk17 : ∀ n < 256, 48640 + n < 177147 →
    row (48640 + n) := by decide +kernel

private theorem chunk18 : ∀ n < 256, 48896 + n < 177147 →
    row (48896 + n) := by decide +kernel

private theorem chunk19 : ∀ n < 256, 49152 + n < 177147 →
    row (49152 + n) := by decide +kernel

private theorem chunk20 : ∀ n < 256, 49408 + n < 177147 →
    row (49408 + n) := by decide +kernel

private theorem chunk21 : ∀ n < 256, 49664 + n < 177147 →
    row (49664 + n) := by decide +kernel

private theorem chunk22 : ∀ n < 256, 49920 + n < 177147 →
    row (49920 + n) := by decide +kernel

private theorem chunk23 : ∀ n < 256, 50176 + n < 177147 →
    row (50176 + n) := by decide +kernel

private theorem chunk24 : ∀ n < 256, 50432 + n < 177147 →
    row (50432 + n) := by decide +kernel

private theorem chunk25 : ∀ n < 256, 50688 + n < 177147 →
    row (50688 + n) := by decide +kernel

private theorem chunk26 : ∀ n < 256, 50944 + n < 177147 →
    row (50944 + n) := by decide +kernel

private theorem chunk27 : ∀ n < 256, 51200 + n < 177147 →
    row (51200 + n) := by decide +kernel

private theorem chunk28 : ∀ n < 256, 51456 + n < 177147 →
    row (51456 + n) := by decide +kernel

private theorem chunk29 : ∀ n < 256, 51712 + n < 177147 →
    row (51712 + n) := by decide +kernel

private theorem chunk30 : ∀ n < 256, 51968 + n < 177147 →
    row (51968 + n) := by decide +kernel

private theorem chunk31 : ∀ n < 256, 52224 + n < 177147 →
    row (52224 + n) := by decide +kernel

private theorem chunk32 : ∀ n < 256, 52480 + n < 177147 →
    row (52480 + n) := by decide +kernel

private theorem chunk33 : ∀ n < 256, 52736 + n < 177147 →
    row (52736 + n) := by decide +kernel

private theorem chunk34 : ∀ n < 256, 52992 + n < 177147 →
    row (52992 + n) := by decide +kernel

private theorem chunk35 : ∀ n < 256, 53248 + n < 177147 →
    row (53248 + n) := by decide +kernel

private theorem chunk36 : ∀ n < 256, 53504 + n < 177147 →
    row (53504 + n) := by decide +kernel

private theorem chunk37 : ∀ n < 256, 53760 + n < 177147 →
    row (53760 + n) := by decide +kernel

private theorem chunk38 : ∀ n < 256, 54016 + n < 177147 →
    row (54016 + n) := by decide +kernel

private theorem chunk39 : ∀ n < 256, 54272 + n < 177147 →
    row (54272 + n) := by decide +kernel

private theorem chunk40 : ∀ n < 256, 54528 + n < 177147 →
    row (54528 + n) := by decide +kernel

private theorem chunk41 : ∀ n < 256, 54784 + n < 177147 →
    row (54784 + n) := by decide +kernel

private theorem chunk42 : ∀ n < 256, 55040 + n < 177147 →
    row (55040 + n) := by decide +kernel

private theorem chunk43 : ∀ n < 256, 55296 + n < 177147 →
    row (55296 + n) := by decide +kernel

private theorem chunk44 : ∀ n < 256, 55552 + n < 177147 →
    row (55552 + n) := by decide +kernel

private theorem chunk45 : ∀ n < 256, 55808 + n < 177147 →
    row (55808 + n) := by decide +kernel

private theorem chunk46 : ∀ n < 256, 56064 + n < 177147 →
    row (56064 + n) := by decide +kernel

private theorem chunk47 : ∀ n < 256, 56320 + n < 177147 →
    row (56320 + n) := by decide +kernel

private theorem chunk48 : ∀ n < 256, 56576 + n < 177147 →
    row (56576 + n) := by decide +kernel

private theorem chunk49 : ∀ n < 256, 56832 + n < 177147 →
    row (56832 + n) := by decide +kernel

private theorem chunk50 : ∀ n < 256, 57088 + n < 177147 →
    row (57088 + n) := by decide +kernel

private theorem chunk51 : ∀ n < 256, 57344 + n < 177147 →
    row (57344 + n) := by decide +kernel

private theorem chunk52 : ∀ n < 256, 57600 + n < 177147 →
    row (57600 + n) := by decide +kernel

private theorem chunk53 : ∀ n < 256, 57856 + n < 177147 →
    row (57856 + n) := by decide +kernel

private theorem chunk54 : ∀ n < 256, 58112 + n < 177147 →
    row (58112 + n) := by decide +kernel

private theorem chunk55 : ∀ n < 256, 58368 + n < 177147 →
    row (58368 + n) := by decide +kernel

private theorem chunk56 : ∀ n < 256, 58624 + n < 177147 →
    row (58624 + n) := by decide +kernel

private theorem chunk57 : ∀ n < 256, 58880 + n < 177147 →
    row (58880 + n) := by decide +kernel

private theorem chunk58 : ∀ n < 256, 59136 + n < 177147 →
    row (59136 + n) := by decide +kernel

private theorem chunk59 : ∀ n < 256, 59392 + n < 177147 →
    row (59392 + n) := by decide +kernel

private theorem chunk60 : ∀ n < 256, 59648 + n < 177147 →
    row (59648 + n) := by decide +kernel

private theorem chunk61 : ∀ n < 256, 59904 + n < 177147 →
    row (59904 + n) := by decide +kernel

private theorem chunk62 : ∀ n < 256, 60160 + n < 177147 →
    row (60160 + n) := by decide +kernel

private theorem chunk63 : ∀ n < 256, 60416 + n < 177147 →
    row (60416 + n) := by decide +kernel

private theorem chunk64 : ∀ n < 256, 60672 + n < 177147 →
    row (60672 + n) := by decide +kernel

private theorem chunk65 : ∀ n < 256, 60928 + n < 177147 →
    row (60928 + n) := by decide +kernel

private theorem chunk66 : ∀ n < 256, 61184 + n < 177147 →
    row (61184 + n) := by decide +kernel

private theorem chunk67 : ∀ n < 256, 61440 + n < 177147 →
    row (61440 + n) := by decide +kernel

private theorem chunk68 : ∀ n < 256, 61696 + n < 177147 →
    row (61696 + n) := by decide +kernel

private theorem chunk69 : ∀ n < 256, 61952 + n < 177147 →
    row (61952 + n) := by decide +kernel

private theorem chunk70 : ∀ n < 256, 62208 + n < 177147 →
    row (62208 + n) := by decide +kernel

private theorem chunk71 : ∀ n < 256, 62464 + n < 177147 →
    row (62464 + n) := by decide +kernel

private theorem chunk72 : ∀ n < 256, 62720 + n < 177147 →
    row (62720 + n) := by decide +kernel

private theorem chunk73 : ∀ n < 256, 62976 + n < 177147 →
    row (62976 + n) := by decide +kernel

private theorem chunk74 : ∀ n < 256, 63232 + n < 177147 →
    row (63232 + n) := by decide +kernel

private theorem chunk75 : ∀ n < 256, 63488 + n < 177147 →
    row (63488 + n) := by decide +kernel

private theorem chunk76 : ∀ n < 256, 63744 + n < 177147 →
    row (63744 + n) := by decide +kernel

private theorem chunk77 : ∀ n < 256, 64000 + n < 177147 →
    row (64000 + n) := by decide +kernel

private theorem chunk78 : ∀ n < 256, 64256 + n < 177147 →
    row (64256 + n) := by decide +kernel

private theorem chunk79 : ∀ n < 256, 64512 + n < 177147 →
    row (64512 + n) := by decide +kernel

private theorem chunk80 : ∀ n < 256, 64768 + n < 177147 →
    row (64768 + n) := by decide +kernel

private theorem chunk81 : ∀ n < 256, 65024 + n < 177147 →
    row (65024 + n) := by decide +kernel

private theorem chunk82 : ∀ n < 256, 65280 + n < 177147 →
    row (65280 + n) := by decide +kernel

private theorem chunk83 : ∀ n < 256, 65536 + n < 177147 →
    row (65536 + n) := by decide +kernel

private theorem chunk84 : ∀ n < 256, 65792 + n < 177147 →
    row (65792 + n) := by decide +kernel

private theorem chunk85 : ∀ n < 256, 66048 + n < 177147 →
    row (66048 + n) := by decide +kernel

private theorem chunk86 : ∀ n < 256, 66304 + n < 177147 →
    row (66304 + n) := by decide +kernel

private theorem chunk87 : ∀ n < 256, 66560 + n < 177147 →
    row (66560 + n) := by decide +kernel

private theorem chunk88 : ∀ n < 256, 66816 + n < 177147 →
    row (66816 + n) := by decide +kernel

private theorem chunk89 : ∀ n < 256, 67072 + n < 177147 →
    row (67072 + n) := by decide +kernel

private theorem chunk90 : ∀ n < 256, 67328 + n < 177147 →
    row (67328 + n) := by decide +kernel

private theorem chunk91 : ∀ n < 256, 67584 + n < 177147 →
    row (67584 + n) := by decide +kernel

private theorem chunk92 : ∀ n < 256, 67840 + n < 177147 →
    row (67840 + n) := by decide +kernel

private theorem chunk93 : ∀ n < 256, 68096 + n < 177147 →
    row (68096 + n) := by decide +kernel

private theorem chunk94 : ∀ n < 256, 68352 + n < 177147 →
    row (68352 + n) := by decide +kernel

private theorem chunk95 : ∀ n < 256, 68608 + n < 177147 →
    row (68608 + n) := by decide +kernel

private theorem chunk96 : ∀ n < 256, 68864 + n < 177147 →
    row (68864 + n) := by decide +kernel

private theorem chunk97 : ∀ n < 256, 69120 + n < 177147 →
    row (69120 + n) := by decide +kernel

private theorem chunk98 : ∀ n < 256, 69376 + n < 177147 →
    row (69376 + n) := by decide +kernel

private theorem chunk99 : ∀ n < 256, 69632 + n < 177147 →
    row (69632 + n) := by decide +kernel

private theorem chunk100 : ∀ n < 256, 69888 + n < 177147 →
    row (69888 + n) := by decide +kernel

private theorem chunk101 : ∀ n < 256, 70144 + n < 177147 →
    row (70144 + n) := by decide +kernel

private theorem chunk102 : ∀ n < 256, 70400 + n < 177147 →
    row (70400 + n) := by decide +kernel

private theorem chunk103 : ∀ n < 256, 70656 + n < 177147 →
    row (70656 + n) := by decide +kernel

private theorem chunk104 : ∀ n < 256, 70912 + n < 177147 →
    row (70912 + n) := by decide +kernel

private theorem chunk105 : ∀ n < 256, 71168 + n < 177147 →
    row (71168 + n) := by decide +kernel

private theorem chunk106 : ∀ n < 256, 71424 + n < 177147 →
    row (71424 + n) := by decide +kernel

private theorem chunk107 : ∀ n < 256, 71680 + n < 177147 →
    row (71680 + n) := by decide +kernel

private theorem chunk108 : ∀ n < 256, 71936 + n < 177147 →
    row (71936 + n) := by decide +kernel

private theorem chunk109 : ∀ n < 256, 72192 + n < 177147 →
    row (72192 + n) := by decide +kernel

private theorem chunk110 : ∀ n < 256, 72448 + n < 177147 →
    row (72448 + n) := by decide +kernel

private theorem chunk111 : ∀ n < 256, 72704 + n < 177147 →
    row (72704 + n) := by decide +kernel

private theorem chunk112 : ∀ n < 256, 72960 + n < 177147 →
    row (72960 + n) := by decide +kernel

private theorem chunk113 : ∀ n < 256, 73216 + n < 177147 →
    row (73216 + n) := by decide +kernel

private theorem chunk114 : ∀ n < 256, 73472 + n < 177147 →
    row (73472 + n) := by decide +kernel

private theorem chunk115 : ∀ n < 256, 73728 + n < 177147 →
    row (73728 + n) := by decide +kernel

private theorem chunk116 : ∀ n < 256, 73984 + n < 177147 →
    row (73984 + n) := by decide +kernel

private theorem chunk117 : ∀ n < 256, 74240 + n < 177147 →
    row (74240 + n) := by decide +kernel

private theorem chunk118 : ∀ n < 256, 74496 + n < 177147 →
    row (74496 + n) := by decide +kernel

private theorem chunk119 : ∀ n < 256, 74752 + n < 177147 →
    row (74752 + n) := by decide +kernel

private theorem chunk120 : ∀ n < 256, 75008 + n < 177147 →
    row (75008 + n) := by decide +kernel

private theorem chunk121 : ∀ n < 256, 75264 + n < 177147 →
    row (75264 + n) := by decide +kernel

private theorem chunk122 : ∀ n < 256, 75520 + n < 177147 →
    row (75520 + n) := by decide +kernel

private theorem chunk123 : ∀ n < 256, 75776 + n < 177147 →
    row (75776 + n) := by decide +kernel

private theorem chunk124 : ∀ n < 256, 76032 + n < 177147 →
    row (76032 + n) := by decide +kernel

private theorem chunk125 : ∀ n < 256, 76288 + n < 177147 →
    row (76288 + n) := by decide +kernel

private theorem chunk126 : ∀ n < 256, 76544 + n < 177147 →
    row (76544 + n) := by decide +kernel

private theorem chunk127 : ∀ n < 256, 76800 + n < 177147 →
    row (76800 + n) := by decide +kernel

private theorem chunk128 : ∀ n < 256, 77056 + n < 177147 →
    row (77056 + n) := by decide +kernel

private theorem chunk129 : ∀ n < 256, 77312 + n < 177147 →
    row (77312 + n) := by decide +kernel

private theorem chunk130 : ∀ n < 256, 77568 + n < 177147 →
    row (77568 + n) := by decide +kernel

private theorem chunk131 : ∀ n < 256, 77824 + n < 177147 →
    row (77824 + n) := by decide +kernel

private theorem chunk132 : ∀ n < 256, 78080 + n < 177147 →
    row (78080 + n) := by decide +kernel

private theorem chunk133 : ∀ n < 256, 78336 + n < 177147 →
    row (78336 + n) := by decide +kernel

private theorem chunk134 : ∀ n < 256, 78592 + n < 177147 →
    row (78592 + n) := by decide +kernel

private theorem chunk135 : ∀ n < 256, 78848 + n < 177147 →
    row (78848 + n) := by decide +kernel

private theorem chunk136 : ∀ n < 256, 79104 + n < 177147 →
    row (79104 + n) := by decide +kernel

private theorem chunk137 : ∀ n < 256, 79360 + n < 177147 →
    row (79360 + n) := by decide +kernel

private theorem chunk138 : ∀ n < 256, 79616 + n < 177147 →
    row (79616 + n) := by decide +kernel

private theorem chunk139 : ∀ n < 256, 79872 + n < 177147 →
    row (79872 + n) := by decide +kernel

private theorem chunk140 : ∀ n < 256, 80128 + n < 177147 →
    row (80128 + n) := by decide +kernel

private theorem chunk141 : ∀ n < 256, 80384 + n < 177147 →
    row (80384 + n) := by decide +kernel

private theorem chunk142 : ∀ n < 256, 80640 + n < 177147 →
    row (80640 + n) := by decide +kernel

private theorem chunk143 : ∀ n < 256, 80896 + n < 177147 →
    row (80896 + n) := by decide +kernel

private theorem chunk144 : ∀ n < 256, 81152 + n < 177147 →
    row (81152 + n) := by decide +kernel

private theorem chunk145 : ∀ n < 256, 81408 + n < 177147 →
    row (81408 + n) := by decide +kernel

private theorem chunk146 : ∀ n < 256, 81664 + n < 177147 →
    row (81664 + n) := by decide +kernel

private theorem chunk147 : ∀ n < 256, 81920 + n < 177147 →
    row (81920 + n) := by decide +kernel

private theorem chunk148 : ∀ n < 256, 82176 + n < 177147 →
    row (82176 + n) := by decide +kernel

private theorem chunk149 : ∀ n < 256, 82432 + n < 177147 →
    row (82432 + n) := by decide +kernel

private theorem chunk150 : ∀ n < 256, 82688 + n < 177147 →
    row (82688 + n) := by decide +kernel

private theorem chunk151 : ∀ n < 256, 82944 + n < 177147 →
    row (82944 + n) := by decide +kernel

private theorem chunk152 : ∀ n < 256, 83200 + n < 177147 →
    row (83200 + n) := by decide +kernel

private theorem chunk153 : ∀ n < 256, 83456 + n < 177147 →
    row (83456 + n) := by decide +kernel

private theorem chunk154 : ∀ n < 256, 83712 + n < 177147 →
    row (83712 + n) := by decide +kernel

private theorem chunk155 : ∀ n < 256, 83968 + n < 177147 →
    row (83968 + n) := by decide +kernel

private theorem chunk156 : ∀ n < 256, 84224 + n < 177147 →
    row (84224 + n) := by decide +kernel

private theorem chunk157 : ∀ n < 256, 84480 + n < 177147 →
    row (84480 + n) := by decide +kernel

private theorem chunk158 : ∀ n < 256, 84736 + n < 177147 →
    row (84736 + n) := by decide +kernel

private theorem chunk159 : ∀ n < 256, 84992 + n < 177147 →
    row (84992 + n) := by decide +kernel

private theorem chunk160 : ∀ n < 256, 85248 + n < 177147 →
    row (85248 + n) := by decide +kernel

private theorem chunk161 : ∀ n < 256, 85504 + n < 177147 →
    row (85504 + n) := by decide +kernel

private theorem chunk162 : ∀ n < 256, 85760 + n < 177147 →
    row (85760 + n) := by decide +kernel

private theorem chunk163 : ∀ n < 256, 86016 + n < 177147 →
    row (86016 + n) := by decide +kernel

private theorem chunk164 : ∀ n < 256, 86272 + n < 177147 →
    row (86272 + n) := by decide +kernel

private theorem chunk165 : ∀ n < 256, 86528 + n < 177147 →
    row (86528 + n) := by decide +kernel

private theorem chunk166 : ∀ n < 256, 86784 + n < 177147 →
    row (86784 + n) := by decide +kernel

private theorem chunk167 : ∀ n < 256, 87040 + n < 177147 →
    row (87040 + n) := by decide +kernel

private theorem chunk168 : ∀ n < 256, 87296 + n < 177147 →
    row (87296 + n) := by decide +kernel

private theorem chunk169 : ∀ n < 256, 87552 + n < 177147 →
    row (87552 + n) := by decide +kernel

private theorem chunk170 : ∀ n < 256, 87808 + n < 177147 →
    row (87808 + n) := by decide +kernel

private theorem chunk171 : ∀ n < 256, 88064 + n < 177147 →
    row (88064 + n) := by decide +kernel

private theorem chunk172 : ∀ n < 256, 88320 + n < 177147 →
    row (88320 + n) := by decide +kernel

theorem checked : ∀ i, 44288 ≤ i → i < 88576 → row i := by
  have hc : ∀ j < 173, ∀ n < 256,
      44288 + 256*j + n < 177147 → row (44288 + 256*j + n) := by
    intro j hj
    interval_cases j
    · exact chunk0
    · exact chunk1
    · exact chunk2
    · exact chunk3
    · exact chunk4
    · exact chunk5
    · exact chunk6
    · exact chunk7
    · exact chunk8
    · exact chunk9
    · exact chunk10
    · exact chunk11
    · exact chunk12
    · exact chunk13
    · exact chunk14
    · exact chunk15
    · exact chunk16
    · exact chunk17
    · exact chunk18
    · exact chunk19
    · exact chunk20
    · exact chunk21
    · exact chunk22
    · exact chunk23
    · exact chunk24
    · exact chunk25
    · exact chunk26
    · exact chunk27
    · exact chunk28
    · exact chunk29
    · exact chunk30
    · exact chunk31
    · exact chunk32
    · exact chunk33
    · exact chunk34
    · exact chunk35
    · exact chunk36
    · exact chunk37
    · exact chunk38
    · exact chunk39
    · exact chunk40
    · exact chunk41
    · exact chunk42
    · exact chunk43
    · exact chunk44
    · exact chunk45
    · exact chunk46
    · exact chunk47
    · exact chunk48
    · exact chunk49
    · exact chunk50
    · exact chunk51
    · exact chunk52
    · exact chunk53
    · exact chunk54
    · exact chunk55
    · exact chunk56
    · exact chunk57
    · exact chunk58
    · exact chunk59
    · exact chunk60
    · exact chunk61
    · exact chunk62
    · exact chunk63
    · exact chunk64
    · exact chunk65
    · exact chunk66
    · exact chunk67
    · exact chunk68
    · exact chunk69
    · exact chunk70
    · exact chunk71
    · exact chunk72
    · exact chunk73
    · exact chunk74
    · exact chunk75
    · exact chunk76
    · exact chunk77
    · exact chunk78
    · exact chunk79
    · exact chunk80
    · exact chunk81
    · exact chunk82
    · exact chunk83
    · exact chunk84
    · exact chunk85
    · exact chunk86
    · exact chunk87
    · exact chunk88
    · exact chunk89
    · exact chunk90
    · exact chunk91
    · exact chunk92
    · exact chunk93
    · exact chunk94
    · exact chunk95
    · exact chunk96
    · exact chunk97
    · exact chunk98
    · exact chunk99
    · exact chunk100
    · exact chunk101
    · exact chunk102
    · exact chunk103
    · exact chunk104
    · exact chunk105
    · exact chunk106
    · exact chunk107
    · exact chunk108
    · exact chunk109
    · exact chunk110
    · exact chunk111
    · exact chunk112
    · exact chunk113
    · exact chunk114
    · exact chunk115
    · exact chunk116
    · exact chunk117
    · exact chunk118
    · exact chunk119
    · exact chunk120
    · exact chunk121
    · exact chunk122
    · exact chunk123
    · exact chunk124
    · exact chunk125
    · exact chunk126
    · exact chunk127
    · exact chunk128
    · exact chunk129
    · exact chunk130
    · exact chunk131
    · exact chunk132
    · exact chunk133
    · exact chunk134
    · exact chunk135
    · exact chunk136
    · exact chunk137
    · exact chunk138
    · exact chunk139
    · exact chunk140
    · exact chunk141
    · exact chunk142
    · exact chunk143
    · exact chunk144
    · exact chunk145
    · exact chunk146
    · exact chunk147
    · exact chunk148
    · exact chunk149
    · exact chunk150
    · exact chunk151
    · exact chunk152
    · exact chunk153
    · exact chunk154
    · exact chunk155
    · exact chunk156
    · exact chunk157
    · exact chunk158
    · exact chunk159
    · exact chunk160
    · exact chunk161
    · exact chunk162
    · exact chunk163
    · exact chunk164
    · exact chunk165
    · exact chunk166
    · exact chunk167
    · exact chunk168
    · exact chunk169
    · exact chunk170
    · exact chunk171
    · exact chunk172
  intro i hlo hhi
  have h := hc ((i-44288)/256) (by omega) ((i-44288)%256) (by omega) (by omega)
  have he : 44288 + 256*((i-44288)/256) + (i-44288)%256 = i := by omega
  simpa only [he] using h

end Problems.Collatz.PreimageCheck12Part1
