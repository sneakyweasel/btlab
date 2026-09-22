import Problems.Collatz.PreimageWeights12

namespace Problems.Collatz.PreimageCheck12Part0
open PreimageWeights12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem chunk0 : ∀ n < 256, 0 + n < 177147 →
    row (0 + n) := by decide +kernel

private theorem chunk1 : ∀ n < 256, 256 + n < 177147 →
    row (256 + n) := by decide +kernel

private theorem chunk2 : ∀ n < 256, 512 + n < 177147 →
    row (512 + n) := by decide +kernel

private theorem chunk3 : ∀ n < 256, 768 + n < 177147 →
    row (768 + n) := by decide +kernel

private theorem chunk4 : ∀ n < 256, 1024 + n < 177147 →
    row (1024 + n) := by decide +kernel

private theorem chunk5 : ∀ n < 256, 1280 + n < 177147 →
    row (1280 + n) := by decide +kernel

private theorem chunk6 : ∀ n < 256, 1536 + n < 177147 →
    row (1536 + n) := by decide +kernel

private theorem chunk7 : ∀ n < 256, 1792 + n < 177147 →
    row (1792 + n) := by decide +kernel

private theorem chunk8 : ∀ n < 256, 2048 + n < 177147 →
    row (2048 + n) := by decide +kernel

private theorem chunk9 : ∀ n < 256, 2304 + n < 177147 →
    row (2304 + n) := by decide +kernel

private theorem chunk10 : ∀ n < 256, 2560 + n < 177147 →
    row (2560 + n) := by decide +kernel

private theorem chunk11 : ∀ n < 256, 2816 + n < 177147 →
    row (2816 + n) := by decide +kernel

private theorem chunk12 : ∀ n < 256, 3072 + n < 177147 →
    row (3072 + n) := by decide +kernel

private theorem chunk13 : ∀ n < 256, 3328 + n < 177147 →
    row (3328 + n) := by decide +kernel

private theorem chunk14 : ∀ n < 256, 3584 + n < 177147 →
    row (3584 + n) := by decide +kernel

private theorem chunk15 : ∀ n < 256, 3840 + n < 177147 →
    row (3840 + n) := by decide +kernel

private theorem chunk16 : ∀ n < 256, 4096 + n < 177147 →
    row (4096 + n) := by decide +kernel

private theorem chunk17 : ∀ n < 256, 4352 + n < 177147 →
    row (4352 + n) := by decide +kernel

private theorem chunk18 : ∀ n < 256, 4608 + n < 177147 →
    row (4608 + n) := by decide +kernel

private theorem chunk19 : ∀ n < 256, 4864 + n < 177147 →
    row (4864 + n) := by decide +kernel

private theorem chunk20 : ∀ n < 256, 5120 + n < 177147 →
    row (5120 + n) := by decide +kernel

private theorem chunk21 : ∀ n < 256, 5376 + n < 177147 →
    row (5376 + n) := by decide +kernel

private theorem chunk22 : ∀ n < 256, 5632 + n < 177147 →
    row (5632 + n) := by decide +kernel

private theorem chunk23 : ∀ n < 256, 5888 + n < 177147 →
    row (5888 + n) := by decide +kernel

private theorem chunk24 : ∀ n < 256, 6144 + n < 177147 →
    row (6144 + n) := by decide +kernel

private theorem chunk25 : ∀ n < 256, 6400 + n < 177147 →
    row (6400 + n) := by decide +kernel

private theorem chunk26 : ∀ n < 256, 6656 + n < 177147 →
    row (6656 + n) := by decide +kernel

private theorem chunk27 : ∀ n < 256, 6912 + n < 177147 →
    row (6912 + n) := by decide +kernel

private theorem chunk28 : ∀ n < 256, 7168 + n < 177147 →
    row (7168 + n) := by decide +kernel

private theorem chunk29 : ∀ n < 256, 7424 + n < 177147 →
    row (7424 + n) := by decide +kernel

private theorem chunk30 : ∀ n < 256, 7680 + n < 177147 →
    row (7680 + n) := by decide +kernel

private theorem chunk31 : ∀ n < 256, 7936 + n < 177147 →
    row (7936 + n) := by decide +kernel

private theorem chunk32 : ∀ n < 256, 8192 + n < 177147 →
    row (8192 + n) := by decide +kernel

private theorem chunk33 : ∀ n < 256, 8448 + n < 177147 →
    row (8448 + n) := by decide +kernel

private theorem chunk34 : ∀ n < 256, 8704 + n < 177147 →
    row (8704 + n) := by decide +kernel

private theorem chunk35 : ∀ n < 256, 8960 + n < 177147 →
    row (8960 + n) := by decide +kernel

private theorem chunk36 : ∀ n < 256, 9216 + n < 177147 →
    row (9216 + n) := by decide +kernel

private theorem chunk37 : ∀ n < 256, 9472 + n < 177147 →
    row (9472 + n) := by decide +kernel

private theorem chunk38 : ∀ n < 256, 9728 + n < 177147 →
    row (9728 + n) := by decide +kernel

private theorem chunk39 : ∀ n < 256, 9984 + n < 177147 →
    row (9984 + n) := by decide +kernel

private theorem chunk40 : ∀ n < 256, 10240 + n < 177147 →
    row (10240 + n) := by decide +kernel

private theorem chunk41 : ∀ n < 256, 10496 + n < 177147 →
    row (10496 + n) := by decide +kernel

private theorem chunk42 : ∀ n < 256, 10752 + n < 177147 →
    row (10752 + n) := by decide +kernel

private theorem chunk43 : ∀ n < 256, 11008 + n < 177147 →
    row (11008 + n) := by decide +kernel

private theorem chunk44 : ∀ n < 256, 11264 + n < 177147 →
    row (11264 + n) := by decide +kernel

private theorem chunk45 : ∀ n < 256, 11520 + n < 177147 →
    row (11520 + n) := by decide +kernel

private theorem chunk46 : ∀ n < 256, 11776 + n < 177147 →
    row (11776 + n) := by decide +kernel

private theorem chunk47 : ∀ n < 256, 12032 + n < 177147 →
    row (12032 + n) := by decide +kernel

private theorem chunk48 : ∀ n < 256, 12288 + n < 177147 →
    row (12288 + n) := by decide +kernel

private theorem chunk49 : ∀ n < 256, 12544 + n < 177147 →
    row (12544 + n) := by decide +kernel

private theorem chunk50 : ∀ n < 256, 12800 + n < 177147 →
    row (12800 + n) := by decide +kernel

private theorem chunk51 : ∀ n < 256, 13056 + n < 177147 →
    row (13056 + n) := by decide +kernel

private theorem chunk52 : ∀ n < 256, 13312 + n < 177147 →
    row (13312 + n) := by decide +kernel

private theorem chunk53 : ∀ n < 256, 13568 + n < 177147 →
    row (13568 + n) := by decide +kernel

private theorem chunk54 : ∀ n < 256, 13824 + n < 177147 →
    row (13824 + n) := by decide +kernel

private theorem chunk55 : ∀ n < 256, 14080 + n < 177147 →
    row (14080 + n) := by decide +kernel

private theorem chunk56 : ∀ n < 256, 14336 + n < 177147 →
    row (14336 + n) := by decide +kernel

private theorem chunk57 : ∀ n < 256, 14592 + n < 177147 →
    row (14592 + n) := by decide +kernel

private theorem chunk58 : ∀ n < 256, 14848 + n < 177147 →
    row (14848 + n) := by decide +kernel

private theorem chunk59 : ∀ n < 256, 15104 + n < 177147 →
    row (15104 + n) := by decide +kernel

private theorem chunk60 : ∀ n < 256, 15360 + n < 177147 →
    row (15360 + n) := by decide +kernel

private theorem chunk61 : ∀ n < 256, 15616 + n < 177147 →
    row (15616 + n) := by decide +kernel

private theorem chunk62 : ∀ n < 256, 15872 + n < 177147 →
    row (15872 + n) := by decide +kernel

private theorem chunk63 : ∀ n < 256, 16128 + n < 177147 →
    row (16128 + n) := by decide +kernel

private theorem chunk64 : ∀ n < 256, 16384 + n < 177147 →
    row (16384 + n) := by decide +kernel

private theorem chunk65 : ∀ n < 256, 16640 + n < 177147 →
    row (16640 + n) := by decide +kernel

private theorem chunk66 : ∀ n < 256, 16896 + n < 177147 →
    row (16896 + n) := by decide +kernel

private theorem chunk67 : ∀ n < 256, 17152 + n < 177147 →
    row (17152 + n) := by decide +kernel

private theorem chunk68 : ∀ n < 256, 17408 + n < 177147 →
    row (17408 + n) := by decide +kernel

private theorem chunk69 : ∀ n < 256, 17664 + n < 177147 →
    row (17664 + n) := by decide +kernel

private theorem chunk70 : ∀ n < 256, 17920 + n < 177147 →
    row (17920 + n) := by decide +kernel

private theorem chunk71 : ∀ n < 256, 18176 + n < 177147 →
    row (18176 + n) := by decide +kernel

private theorem chunk72 : ∀ n < 256, 18432 + n < 177147 →
    row (18432 + n) := by decide +kernel

private theorem chunk73 : ∀ n < 256, 18688 + n < 177147 →
    row (18688 + n) := by decide +kernel

private theorem chunk74 : ∀ n < 256, 18944 + n < 177147 →
    row (18944 + n) := by decide +kernel

private theorem chunk75 : ∀ n < 256, 19200 + n < 177147 →
    row (19200 + n) := by decide +kernel

private theorem chunk76 : ∀ n < 256, 19456 + n < 177147 →
    row (19456 + n) := by decide +kernel

private theorem chunk77 : ∀ n < 256, 19712 + n < 177147 →
    row (19712 + n) := by decide +kernel

private theorem chunk78 : ∀ n < 256, 19968 + n < 177147 →
    row (19968 + n) := by decide +kernel

private theorem chunk79 : ∀ n < 256, 20224 + n < 177147 →
    row (20224 + n) := by decide +kernel

private theorem chunk80 : ∀ n < 256, 20480 + n < 177147 →
    row (20480 + n) := by decide +kernel

private theorem chunk81 : ∀ n < 256, 20736 + n < 177147 →
    row (20736 + n) := by decide +kernel

private theorem chunk82 : ∀ n < 256, 20992 + n < 177147 →
    row (20992 + n) := by decide +kernel

private theorem chunk83 : ∀ n < 256, 21248 + n < 177147 →
    row (21248 + n) := by decide +kernel

private theorem chunk84 : ∀ n < 256, 21504 + n < 177147 →
    row (21504 + n) := by decide +kernel

private theorem chunk85 : ∀ n < 256, 21760 + n < 177147 →
    row (21760 + n) := by decide +kernel

private theorem chunk86 : ∀ n < 256, 22016 + n < 177147 →
    row (22016 + n) := by decide +kernel

private theorem chunk87 : ∀ n < 256, 22272 + n < 177147 →
    row (22272 + n) := by decide +kernel

private theorem chunk88 : ∀ n < 256, 22528 + n < 177147 →
    row (22528 + n) := by decide +kernel

private theorem chunk89 : ∀ n < 256, 22784 + n < 177147 →
    row (22784 + n) := by decide +kernel

private theorem chunk90 : ∀ n < 256, 23040 + n < 177147 →
    row (23040 + n) := by decide +kernel

private theorem chunk91 : ∀ n < 256, 23296 + n < 177147 →
    row (23296 + n) := by decide +kernel

private theorem chunk92 : ∀ n < 256, 23552 + n < 177147 →
    row (23552 + n) := by decide +kernel

private theorem chunk93 : ∀ n < 256, 23808 + n < 177147 →
    row (23808 + n) := by decide +kernel

private theorem chunk94 : ∀ n < 256, 24064 + n < 177147 →
    row (24064 + n) := by decide +kernel

private theorem chunk95 : ∀ n < 256, 24320 + n < 177147 →
    row (24320 + n) := by decide +kernel

private theorem chunk96 : ∀ n < 256, 24576 + n < 177147 →
    row (24576 + n) := by decide +kernel

private theorem chunk97 : ∀ n < 256, 24832 + n < 177147 →
    row (24832 + n) := by decide +kernel

private theorem chunk98 : ∀ n < 256, 25088 + n < 177147 →
    row (25088 + n) := by decide +kernel

private theorem chunk99 : ∀ n < 256, 25344 + n < 177147 →
    row (25344 + n) := by decide +kernel

private theorem chunk100 : ∀ n < 256, 25600 + n < 177147 →
    row (25600 + n) := by decide +kernel

private theorem chunk101 : ∀ n < 256, 25856 + n < 177147 →
    row (25856 + n) := by decide +kernel

private theorem chunk102 : ∀ n < 256, 26112 + n < 177147 →
    row (26112 + n) := by decide +kernel

private theorem chunk103 : ∀ n < 256, 26368 + n < 177147 →
    row (26368 + n) := by decide +kernel

private theorem chunk104 : ∀ n < 256, 26624 + n < 177147 →
    row (26624 + n) := by decide +kernel

private theorem chunk105 : ∀ n < 256, 26880 + n < 177147 →
    row (26880 + n) := by decide +kernel

private theorem chunk106 : ∀ n < 256, 27136 + n < 177147 →
    row (27136 + n) := by decide +kernel

private theorem chunk107 : ∀ n < 256, 27392 + n < 177147 →
    row (27392 + n) := by decide +kernel

private theorem chunk108 : ∀ n < 256, 27648 + n < 177147 →
    row (27648 + n) := by decide +kernel

private theorem chunk109 : ∀ n < 256, 27904 + n < 177147 →
    row (27904 + n) := by decide +kernel

private theorem chunk110 : ∀ n < 256, 28160 + n < 177147 →
    row (28160 + n) := by decide +kernel

private theorem chunk111 : ∀ n < 256, 28416 + n < 177147 →
    row (28416 + n) := by decide +kernel

private theorem chunk112 : ∀ n < 256, 28672 + n < 177147 →
    row (28672 + n) := by decide +kernel

private theorem chunk113 : ∀ n < 256, 28928 + n < 177147 →
    row (28928 + n) := by decide +kernel

private theorem chunk114 : ∀ n < 256, 29184 + n < 177147 →
    row (29184 + n) := by decide +kernel

private theorem chunk115 : ∀ n < 256, 29440 + n < 177147 →
    row (29440 + n) := by decide +kernel

private theorem chunk116 : ∀ n < 256, 29696 + n < 177147 →
    row (29696 + n) := by decide +kernel

private theorem chunk117 : ∀ n < 256, 29952 + n < 177147 →
    row (29952 + n) := by decide +kernel

private theorem chunk118 : ∀ n < 256, 30208 + n < 177147 →
    row (30208 + n) := by decide +kernel

private theorem chunk119 : ∀ n < 256, 30464 + n < 177147 →
    row (30464 + n) := by decide +kernel

private theorem chunk120 : ∀ n < 256, 30720 + n < 177147 →
    row (30720 + n) := by decide +kernel

private theorem chunk121 : ∀ n < 256, 30976 + n < 177147 →
    row (30976 + n) := by decide +kernel

private theorem chunk122 : ∀ n < 256, 31232 + n < 177147 →
    row (31232 + n) := by decide +kernel

private theorem chunk123 : ∀ n < 256, 31488 + n < 177147 →
    row (31488 + n) := by decide +kernel

private theorem chunk124 : ∀ n < 256, 31744 + n < 177147 →
    row (31744 + n) := by decide +kernel

private theorem chunk125 : ∀ n < 256, 32000 + n < 177147 →
    row (32000 + n) := by decide +kernel

private theorem chunk126 : ∀ n < 256, 32256 + n < 177147 →
    row (32256 + n) := by decide +kernel

private theorem chunk127 : ∀ n < 256, 32512 + n < 177147 →
    row (32512 + n) := by decide +kernel

private theorem chunk128 : ∀ n < 256, 32768 + n < 177147 →
    row (32768 + n) := by decide +kernel

private theorem chunk129 : ∀ n < 256, 33024 + n < 177147 →
    row (33024 + n) := by decide +kernel

private theorem chunk130 : ∀ n < 256, 33280 + n < 177147 →
    row (33280 + n) := by decide +kernel

private theorem chunk131 : ∀ n < 256, 33536 + n < 177147 →
    row (33536 + n) := by decide +kernel

private theorem chunk132 : ∀ n < 256, 33792 + n < 177147 →
    row (33792 + n) := by decide +kernel

private theorem chunk133 : ∀ n < 256, 34048 + n < 177147 →
    row (34048 + n) := by decide +kernel

private theorem chunk134 : ∀ n < 256, 34304 + n < 177147 →
    row (34304 + n) := by decide +kernel

private theorem chunk135 : ∀ n < 256, 34560 + n < 177147 →
    row (34560 + n) := by decide +kernel

private theorem chunk136 : ∀ n < 256, 34816 + n < 177147 →
    row (34816 + n) := by decide +kernel

private theorem chunk137 : ∀ n < 256, 35072 + n < 177147 →
    row (35072 + n) := by decide +kernel

private theorem chunk138 : ∀ n < 256, 35328 + n < 177147 →
    row (35328 + n) := by decide +kernel

private theorem chunk139 : ∀ n < 256, 35584 + n < 177147 →
    row (35584 + n) := by decide +kernel

private theorem chunk140 : ∀ n < 256, 35840 + n < 177147 →
    row (35840 + n) := by decide +kernel

private theorem chunk141 : ∀ n < 256, 36096 + n < 177147 →
    row (36096 + n) := by decide +kernel

private theorem chunk142 : ∀ n < 256, 36352 + n < 177147 →
    row (36352 + n) := by decide +kernel

private theorem chunk143 : ∀ n < 256, 36608 + n < 177147 →
    row (36608 + n) := by decide +kernel

private theorem chunk144 : ∀ n < 256, 36864 + n < 177147 →
    row (36864 + n) := by decide +kernel

private theorem chunk145 : ∀ n < 256, 37120 + n < 177147 →
    row (37120 + n) := by decide +kernel

private theorem chunk146 : ∀ n < 256, 37376 + n < 177147 →
    row (37376 + n) := by decide +kernel

private theorem chunk147 : ∀ n < 256, 37632 + n < 177147 →
    row (37632 + n) := by decide +kernel

private theorem chunk148 : ∀ n < 256, 37888 + n < 177147 →
    row (37888 + n) := by decide +kernel

private theorem chunk149 : ∀ n < 256, 38144 + n < 177147 →
    row (38144 + n) := by decide +kernel

private theorem chunk150 : ∀ n < 256, 38400 + n < 177147 →
    row (38400 + n) := by decide +kernel

private theorem chunk151 : ∀ n < 256, 38656 + n < 177147 →
    row (38656 + n) := by decide +kernel

private theorem chunk152 : ∀ n < 256, 38912 + n < 177147 →
    row (38912 + n) := by decide +kernel

private theorem chunk153 : ∀ n < 256, 39168 + n < 177147 →
    row (39168 + n) := by decide +kernel

private theorem chunk154 : ∀ n < 256, 39424 + n < 177147 →
    row (39424 + n) := by decide +kernel

private theorem chunk155 : ∀ n < 256, 39680 + n < 177147 →
    row (39680 + n) := by decide +kernel

private theorem chunk156 : ∀ n < 256, 39936 + n < 177147 →
    row (39936 + n) := by decide +kernel

private theorem chunk157 : ∀ n < 256, 40192 + n < 177147 →
    row (40192 + n) := by decide +kernel

private theorem chunk158 : ∀ n < 256, 40448 + n < 177147 →
    row (40448 + n) := by decide +kernel

private theorem chunk159 : ∀ n < 256, 40704 + n < 177147 →
    row (40704 + n) := by decide +kernel

private theorem chunk160 : ∀ n < 256, 40960 + n < 177147 →
    row (40960 + n) := by decide +kernel

private theorem chunk161 : ∀ n < 256, 41216 + n < 177147 →
    row (41216 + n) := by decide +kernel

private theorem chunk162 : ∀ n < 256, 41472 + n < 177147 →
    row (41472 + n) := by decide +kernel

private theorem chunk163 : ∀ n < 256, 41728 + n < 177147 →
    row (41728 + n) := by decide +kernel

private theorem chunk164 : ∀ n < 256, 41984 + n < 177147 →
    row (41984 + n) := by decide +kernel

private theorem chunk165 : ∀ n < 256, 42240 + n < 177147 →
    row (42240 + n) := by decide +kernel

private theorem chunk166 : ∀ n < 256, 42496 + n < 177147 →
    row (42496 + n) := by decide +kernel

private theorem chunk167 : ∀ n < 256, 42752 + n < 177147 →
    row (42752 + n) := by decide +kernel

private theorem chunk168 : ∀ n < 256, 43008 + n < 177147 →
    row (43008 + n) := by decide +kernel

private theorem chunk169 : ∀ n < 256, 43264 + n < 177147 →
    row (43264 + n) := by decide +kernel

private theorem chunk170 : ∀ n < 256, 43520 + n < 177147 →
    row (43520 + n) := by decide +kernel

private theorem chunk171 : ∀ n < 256, 43776 + n < 177147 →
    row (43776 + n) := by decide +kernel

private theorem chunk172 : ∀ n < 256, 44032 + n < 177147 →
    row (44032 + n) := by decide +kernel

theorem checked : ∀ i, 0 ≤ i → i < 44288 → row i := by
  have hc : ∀ j < 173, ∀ n < 256,
      0 + 256*j + n < 177147 → row (0 + 256*j + n) := by
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
  have h := hc ((i-0)/256) (by omega) ((i-0)%256) (by omega) (by omega)
  have he : 0 + 256*((i-0)/256) + (i-0)%256 = i := by omega
  simpa only [he] using h

end Problems.Collatz.PreimageCheck12Part0
