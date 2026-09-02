# Juggler long-excursion transfer

Status: **EXCURSION_TRANSFER_CLOSED**

Numerical (L, H, L') transfer of complete record excursions.
Not a halt theorem. Absence is NOT_OBSERVED_WITHIN_BOUND.

## Branch budget

```text
Mathematical target     hold-out-stable transfer / compensation law
Novelty hypothesis      the peak H constrains the next source
Maximum Phase-0 scope   streamed (L,H,L',r); hold-out by start n
```

## Metadata

- classification: **EXCURSION_TRANSFER_CLOSED**
- n_max: `20000000` hold_split: `10000000`
- starts: `9999999` excursions: `16333230` pairs: `6352626`
- bit_cap starts: `142302` horizon: `0`
- grew / declined / growth-growth: `4596421` / `11736809` / `1237620`
- max r: `11` Return A differs: `5130806`
- exact source repeat: `0`
- Return B is Q on 37: `True`
- envelope dominated: `True`
- hold-out stable: `True`
- all integer candidates fail: `True`

Return B is the Q-source chain; every tested one-step, two-step, compensation, and weighted inequality has a counterexample; growth can follow growth; r-bin envelopes stay under the formal 3^r/2^{r+1} scale; no exact source recurrence.

## Laboratories

- 37 sources: `[37, 9317, 2233]`
- 365 sources: `[365, 763, 1749, 4447, 12707]`

- `37`: status=`RETURNED` sources=`[37, 9317, 2233]` excursions=`3`
- `69`: status=`RETURNED` sources=`[69, 117]` excursions=`2`
- `89`: status=`RETURNED` sources=`[89, 155, 291]` excursions=`3`
- `365`: status=`RETURNED` sources=`[365, 763, 1749, 4447, 12707]` excursions=`5`
- `501`: status=`RETURNED` sources=`[501, 1089, 133347, 763, 1749, 4447, 12707]` excursions=`7`
- `1517`: status=`RETURNED` sources=`[1517, 3789, 10613, 33811, 2493]` excursions=`5`
- `6187`: status=`RETURNED` sources=`[6187, 18425, 15771571, 11189]` excursions=`4`
- `329`: status=`RETURNED` sources=`[329, 180370579261640036336071806107777, 1941719144218166368455510841464890645, 258288373266707936943, 45137689]` excursions=`5`
- `33391`: status=`RETURNED` sources=`[33391, 122767, 387101869, 67709, 1481427049, 2988979632820247, 57362255889649668320284478577777206022132264850029018219067, 1574703]` excursions=`8`

## r-bin versus formal scale

- r=`1` n=`8239771` sup_c=`0.750000` formal=`0.750000` slack=`-0.000000`
- r=`2` n=`4113460` sup_c=`1.125000` formal=`1.125000` slack=`-0.000000`
- r=`3` n=`2047154` sup_c=`1.687500` formal=`1.687500` slack=`-0.000000`
- r=`4` n=`1011081` sup_c=`2.531250` formal=`2.531250` slack=`-0.000000`
- r=`5` n=`495970` sup_c=`3.796875` formal=`3.796875` slack=`-0.000000`
- r=`6` n=`239484` sup_c=`5.695313` formal=`5.695312` slack=`-0.000000`
- r=`7` n=`112784` sup_c=`8.542969` formal=`8.542969` slack=`-0.000000`
- r=`8` n=`51457` sup_c=`12.814453` formal=`12.814453` slack=`-0.000000`
- r=`9` n=`21955` sup_c=`19.221680` formal=`19.221680` slack=`-0.000000`
- r=`10` n=`113` sup_c=`28.832520` formal=`28.832520` slack=`0.000000`
- r=`11` n=`1` sup_c=`21.624332` formal=`43.248779` slack=`21.624448`

## Scale bins

- 10^0: count=`4` sup_rho=`1.22222` sup_c=`1.091329` grew=`1`
- 10^1: count=`47` sup_rho=`251.811` sup_c=`2.531100` grew=`10`
- 10^2: count=`490` sup_rho=`1.55536e+58` sup_c=`21.624332` grew=`135`
- 10^3: count=`4830` sup_rho=`1.53332e+105` sup_c=`28.832517` grew=`1362`
- 10^4: count=`47417` sup_rho=`6.33536e+138` sup_c=`28.832520` grew=`13530`
- 10^5: count=`468339` sup_rho=`2.31559e+148` sup_c=`28.832520` grew=`133548`
- 10^6: count=`4642117` sup_rho=`3.55825e+127` sup_c=`19.221680` grew=`1322599`
- 10^7: count=`5955908` sup_rho=`5.93009e+145` sup_c=`19.221680` grew=`1696995`
- 10^8: count=`869039` sup_rho=`1.27151e+146` sup_c=`19.221680` grew=`246473`
- 10^9: count=`393598` sup_rho=`1.3233e+118` sup_c=`12.814453` grew=`111113`
- 10^10: count=`295972` sup_rho=`8.9867e+129` sup_c=`12.814453` grew=`83736`
- 10^11: count=`466568` sup_rho=`5.8994e+141` sup_c=`12.814453` grew=`132114`
- 10^12: count=`398723` sup_rho=`1.18361e+142` sup_c=`12.814453` grew=`112095`
- 10^13: count=`291196` sup_rho=`3.8521e+105` sup_c=`8.542969` grew=`81769`
- 10^14: count=`133326` sup_rho=`1.38838e+113` sup_c=`8.542969` grew=`37679`
- 10^15: count=`152124` sup_rho=`4.80249e+120` sup_c=`8.542969` grew=`42517`
- 10^16: count=`130370` sup_rho=`1.69106e+128` sup_c=`8.542969` grew=`36813`
- 10^17: count=`205998` sup_rho=`5.76068e+135` sup_c=`8.542969` grew=`57943`
- 10^18: count=`183666` sup_rho=`1.20562e+136` sup_c=`8.542969` grew=`50697`
- 10^19: count=`113629` sup_rho=`7.82403e+93` sup_c=`5.695313` grew=`31260`
- 10^20: count=`130907` sup_rho=`3.95386e+98` sup_c=`5.695313` grew=`36434`
- 10^21: count=`59061` sup_rho=`1.95212e+103` sup_c=`5.695313` grew=`16132`
- 10^22: count=`75441` sup_rho=`9.76925e+107` sup_c=`5.695313` grew=`20771`
- 10^23: count=`64929` sup_rho=`4.74081e+112` sup_c=`5.695313` grew=`17985`
- 10^24: count=`54483` sup_rho=`2.40062e+117` sup_c=`5.695313` grew=`15188`
- 10^25: count=`70032` sup_rho=`1.13684e+122` sup_c=`5.695313` grew=`19196`
- 10^26: count=`82369` sup_rho=`5.85665e+126` sup_c=`5.695313` grew=`22780`
- 10^27: count=`86949` sup_rho=`1.12824e+127` sup_c=`5.695313` grew=`23201`
- 10^28: count=`40352` sup_rho=`1.28407e+81` sup_c=`3.796875` grew=`10678`
- 10^29: count=`51759` sup_rho=`7.86232e+83` sup_c=`3.796875` grew=`13763`
- 10^30: count=`59079` sup_rho=`5.02709e+86` sup_c=`3.796875` grew=`15642`
- 10^31: count=`33381` sup_rho=`2.96048e+89` sup_c=`3.796875` grew=`8946`
- 10^32: count=`29017` sup_rho=`1.97944e+92` sup_c=`3.796875` grew=`7779`
- 10^33: count=`31698` sup_rho=`1.22238e+95` sup_c=`3.796875` grew=`8463`
- 10^34: count=`40794` sup_rho=`7.76933e+97` sup_c=`3.796875` grew=`10827`
- 10^35: count=`19706` sup_rho=`4.85904e+100` sup_c=`3.796875` grew=`5160`
- 10^36: count=`20961` sup_rho=`3.00969e+103` sup_c=`3.796875` grew=`5515`
- 10^37: count=`25316` sup_rho=`1.88115e+106` sup_c=`3.796875` grew=`6866`
- 10^38: count=`30462` sup_rho=`1.1889e+109` sup_c=`3.796875` grew=`8069`
- 10^39: count=`31586` sup_rho=`7.45619e+111` sup_c=`3.796875` grew=`8401`
- 10^40: count=`30040` sup_rho=`3.28997e+113` sup_c=`3.796875` grew=`7719`
- 10^41: count=`29562` sup_rho=`2.04705e+64` sup_c=`2.531250` grew=`7270`
- 10^42: count=`15456` sup_rho=`6.96845e+65` sup_c=`2.531250` grew=`3900`
- 10^43: count=`19975` sup_rho=`2.36608e+67` sup_c=`2.531250` grew=`4894`
- 10^44: count=`20326` sup_rho=`7.97985e+68` sup_c=`2.531250` grew=`5050`
- 10^45: count=`20713` sup_rho=`2.73315e+70` sup_c=`2.531250` grew=`5140`
- 10^46: count=`23676` sup_rho=`9.17695e+71` sup_c=`2.531250` grew=`5917`
- 10^47: count=`9453` sup_rho=`3.14411e+73` sup_c=`2.531250` grew=`2323`
- 10^48: count=`10931` sup_rho=`1.07075e+75` sup_c=`2.531250` grew=`2726`
- 10^49: count=`14409` sup_rho=`3.64839e+76` sup_c=`2.531250` grew=`3653`
- 10^50: count=`11633` sup_rho=`1.24041e+78` sup_c=`2.531250` grew=`2994`
- 10^51: count=`14932` sup_rho=`4.21285e+79` sup_c=`2.531250` grew=`3730`
- 10^52: count=`14373` sup_rho=`1.40698e+81` sup_c=`2.531250` grew=`3730`
- 10^53: count=`6635` sup_rho=`4.81121e+82` sup_c=`2.531250` grew=`1703`
- 10^54: count=`7657` sup_rho=`1.6431e+84` sup_c=`2.531250` grew=`1890`
- 10^55: count=`10105` sup_rho=`5.59968e+85` sup_c=`2.531250` grew=`2599`
- 10^56: count=`9450` sup_rho=`1.90633e+87` sup_c=`2.531250` grew=`2251`
- 10^57: count=`10723` sup_rho=`6.48433e+88` sup_c=`2.531250` grew=`2739`
- 10^58: count=`13578` sup_rho=`2.1694e+90` sup_c=`2.531250` grew=`3409`
- 10^59: count=`10047` sup_rho=`7.34337e+91` sup_c=`2.531250` grew=`2551`
- 10^60: count=`9634` sup_rho=`1.72593e+93` sup_c=`2.531250` grew=`2356`
- 10^61: count=`11914` sup_rho=`4.20842e+42` sup_c=`1.687500` grew=`2514`
- 10^62: count=`9161` sup_rho=`2.02146e+43` sup_c=`1.687500` grew=`1982`
- 10^63: count=`5627` sup_rho=`9.9998e+43` sup_c=`1.687500` grew=`1211`
- 10^64: count=`6468` sup_rho=`4.82469e+44` sup_c=`1.687500` grew=`1338`
- 10^65: count=`7847` sup_rho=`2.3678e+45` sup_c=`1.687500` grew=`1654`
- 10^66: count=`8017` sup_rho=`1.15364e+46` sup_c=`1.687500` grew=`1665`
- 10^67: count=`6621` sup_rho=`5.60403e+46` sup_c=`1.687500` grew=`1426`
- 10^68: count=`7819` sup_rho=`2.70921e+47` sup_c=`1.687500` grew=`1681`
- 10^69: count=`10046` sup_rho=`1.33078e+48` sup_c=`1.687500` grew=`2087`
- 10^70: count=`5075` sup_rho=`6.40633e+48` sup_c=`1.687500` grew=`1039`
- 10^71: count=`3443` sup_rho=`3.1059e+49` sup_c=`1.687500` grew=`734`
- 10^72: count=`3907` sup_rho=`1.52896e+50` sup_c=`1.687500` grew=`806`
- 10^73: count=`4720` sup_rho=`7.44097e+50` sup_c=`1.687500` grew=`1018`
- 10^74: count=`5671` sup_rho=`3.63401e+51` sup_c=`1.687500` grew=`1242`
- 10^75: count=`4096` sup_rho=`1.77262e+52` sup_c=`1.687500` grew=`839`
- 10^76: count=`4781` sup_rho=`8.62653e+52` sup_c=`1.687500` grew=`1020`
- 10^77: count=`4954` sup_rho=`4.20069e+53` sup_c=`1.687500` grew=`1104`
- 10^78: count=`5685` sup_rho=`2.04843e+54` sup_c=`1.687500` grew=`1249`
- 10^79: count=`2088` sup_rho=`9.99385e+54` sup_c=`1.687500` grew=`436`
- 10^80: count=`2014` sup_rho=`4.83497e+55` sup_c=`1.687500` grew=`427`
- 10^81: count=`2277` sup_rho=`2.37115e+56` sup_c=`1.687500` grew=`488`
- 10^82: count=`2769` sup_rho=`1.15194e+57` sup_c=`1.687500` grew=`587`
- 10^83: count=`3427` sup_rho=`5.60294e+57` sup_c=`1.687500` grew=`752`
- 10^84: count=`3021` sup_rho=`2.73343e+58` sup_c=`1.687500` grew=`659`
- 10^85: count=`3062` sup_rho=`1.31493e+59` sup_c=`1.687500` grew=`659`
- 10^86: count=`3538` sup_rho=`6.25721e+59` sup_c=`1.687500` grew=`772`
- 10^87: count=`4066` sup_rho=`3.15583e+60` sup_c=`1.687500` grew=`835`
- 10^88: count=`4238` sup_rho=`1.53418e+61` sup_c=`1.687500` grew=`939`
- 10^89: count=`2806` sup_rho=`7.44895e+61` sup_c=`1.687500` grew=`593`
- 10^90: count=`2974` sup_rho=`3.64031e+62` sup_c=`1.687500` grew=`626`
- 10^91: count=`3132` sup_rho=`6.11623e+62` sup_c=`1.687500` grew=`569`
- 10^92: count=`3631` sup_rho=`4.21601e+11` sup_c=`1.125000` grew=`608`
- 10^93: count=`2999` sup_rho=`5.61954e+11` sup_c=`1.125000` grew=`535`
- 10^94: count=`1868` sup_rho=`7.4907e+11` sup_c=`1.125000` grew=`308`
- 10^95: count=`1453` sup_rho=`9.99985e+11` sup_c=`1.125000` grew=`242`
- 10^96: count=`1773` sup_rho=`1.33306e+12` sup_c=`1.125000` grew=`320`
- 10^97: count=`1969` sup_rho=`1.77744e+12` sup_c=`1.125000` grew=`313`
- 10^98: count=`2291` sup_rho=`2.37116e+12` sup_c=`1.125000` grew=`374`
- 10^99: count=`2601` sup_rho=`3.16057e+12` sup_c=`1.125000` grew=`454`
- 10^100: count=`1749` sup_rho=`4.21546e+12` sup_c=`1.125000` grew=`307`
- 10^101: count=`1951` sup_rho=`5.62206e+12` sup_c=`1.125000` grew=`321`
- 10^102: count=`2156` sup_rho=`7.4955e+12` sup_c=`1.125000` grew=`336`
- 10^103: count=`2603` sup_rho=`9.99941e+12` sup_c=`1.125000` grew=`451`
- 10^104: count=`2893` sup_rho=`1.33306e+13` sup_c=`1.125000` grew=`471`
- 10^105: count=`1601` sup_rho=`1.77249e+13` sup_c=`1.125000` grew=`278`
- 10^106: count=`1101` sup_rho=`2.37e+13` sup_c=`1.125000` grew=`189`
- 10^107: count=`1030` sup_rho=`3.16226e+13` sup_c=`1.125000` grew=`160`
- 10^108: count=`1088` sup_rho=`4.21095e+13` sup_c=`1.125000` grew=`179`
- 10^109: count=`1219` sup_rho=`5.60433e+13` sup_c=`1.125000` grew=`198`
- 10^110: count=`1438` sup_rho=`7.48937e+13` sup_c=`1.125000` grew=`244`
- 10^111: count=`1682` sup_rho=`9.994e+13` sup_c=`1.125000` grew=`261`
- 10^112: count=`1390` sup_rho=`1.32866e+14` sup_c=`1.125000` grew=`239`
- 10^113: count=`1245` sup_rho=`1.77753e+14` sup_c=`1.125000` grew=`190`
- 10^114: count=`1326` sup_rho=`2.36424e+14` sup_c=`1.125000` grew=`212`
- 10^115: count=`1351` sup_rho=`3.15962e+14` sup_c=`1.125000` grew=`219`
- 10^116: count=`1448` sup_rho=`4.21679e+14` sup_c=`1.125000` grew=`230`
- 10^117: count=`1627` sup_rho=`5.61403e+14` sup_c=`1.125000` grew=`279`
- 10^118: count=`1103` sup_rho=`7.44242e+14` sup_c=`1.125000` grew=`177`
- 10^119: count=`657` sup_rho=`9.99962e+14` sup_c=`1.125000` grew=`127`
- 10^120: count=`559` sup_rho=`1.33133e+15` sup_c=`1.125000` grew=`101`
- 10^121: count=`609` sup_rho=`1.77712e+15` sup_c=`1.125000` grew=`107`
- 10^122: count=`659` sup_rho=`2.36642e+15` sup_c=`1.125000` grew=`134`
- 10^123: count=`748` sup_rho=`3.15192e+15` sup_c=`1.125000` grew=`125`
- 10^124: count=`863` sup_rho=`4.21523e+15` sup_c=`1.125000` grew=`146`
- 10^125: count=`950` sup_rho=`5.61303e+15` sup_c=`1.125000` grew=`138`
- 10^126: count=`884` sup_rho=`7.49815e+15` sup_c=`1.125000` grew=`134`
- 10^127: count=`770` sup_rho=`9.98198e+15` sup_c=`1.125000` grew=`122`
- 10^128: count=`881` sup_rho=`1.3273e+16` sup_c=`1.125000` grew=`151`
- 10^129: count=`998` sup_rho=`1.77692e+16` sup_c=`1.125000` grew=`152`
- 10^130: count=`1123` sup_rho=`2.36982e+16` sup_c=`1.125000` grew=`206`
- 10^131: count=`1211` sup_rho=`3.16212e+16` sup_c=`1.125000` grew=`205`
- 10^132: count=`1334` sup_rho=`4.21494e+16` sup_c=`1.125000` grew=`198`
- 10^133: count=`887` sup_rho=`5.59766e+16` sup_c=`1.125000` grew=`155`
- 10^134: count=`850` sup_rho=`7.47952e+16` sup_c=`1.125000` grew=`143`
- 10^135: count=`779` sup_rho=`9.98208e+16` sup_c=`1.125000` grew=`136`
- 10^136: count=`957` sup_rho=`1.33282e+17` sup_c=`1.125000` grew=`165`
- 10^137: count=`717` sup_rho=`1.33359e+17` sup_c=`1.125000` grew=`1`
- 10^138: count=`794` sup_rho=`3.16227e-35` sup_c=`0.750000` grew=`0`
- 10^139: count=`837` sup_rho=`1.7775e-35` sup_c=`0.750000` grew=`0`
- 10^140: count=`549` sup_rho=`9.98795e-36` sup_c=`0.750000` grew=`0`
- 10^141: count=`412` sup_rho=`5.59496e-36` sup_c=`0.750000` grew=`0`
- 10^142: count=`358` sup_rho=`3.15155e-36` sup_c=`0.750000` grew=`0`
- 10^143: count=`360` sup_rho=`1.77753e-36` sup_c=`0.750000` grew=`0`
- 10^144: count=`380` sup_rho=`9.98831e-37` sup_c=`0.750000` grew=`0`
- 10^145: count=`419` sup_rho=`5.61679e-37` sup_c=`0.750000` grew=`0`
- 10^146: count=`461` sup_rho=`3.15902e-37` sup_c=`0.750000` grew=`0`
- 10^147: count=`535` sup_rho=`1.76914e-37` sup_c=`0.750000` grew=`0`
- 10^148: count=`565` sup_rho=`9.98132e-38` sup_c=`0.750000` grew=`0`
- 10^149: count=`595` sup_rho=`5.60294e-38` sup_c=`0.750000` grew=`0`
- 10^150: count=`396` sup_rho=`3.13949e-38` sup_c=`0.750000` grew=`0`
- 10^151: count=`438` sup_rho=`1.77798e-38` sup_c=`0.750000` grew=`0`
- 10^152: count=`402` sup_rho=`9.98541e-39` sup_c=`0.750000` grew=`0`
- 10^153: count=`434` sup_rho=`5.61744e-39` sup_c=`0.750000` grew=`0`
- 10^154: count=`58` sup_rho=`3.15966e-39` sup_c=`0.750000` grew=`0`

## Integer candidates (first counterexample)

- `L2_lt_L0`: fails=`2320902` ce=`{'n': 37, 'L0': 37, 'H': 86818724, 'L1': 9317, 'L2': 2233, 'r0': 4, 'r1': 3}`
- `L2_lt_L1`: fails=`1751940` ce=`{'n': 89, 'L0': 89, 'H': 24302, 'L1': 155, 'L2': 291, 'r0': 2, 'r1': 2}`
- `L0_L2_lt_L1_sq`: fails=`2194501` ce=`{'n': 89, 'L0': 89, 'H': 24302, 'L1': 155, 'L2': 291, 'r0': 2, 'r1': 2}`
- `L2_sq_lt_L0_L1`: fails=`1869894` ce=`{'n': 37, 'L0': 37, 'H': 86818724, 'L1': 9317, 'L2': 2233, 'r0': 4, 'r1': 3}`
- `L1_L2_lt_L0_cu`: fails=`1775769` ce=`{'n': 37, 'L0': 37, 'H': 86818724, 'L1': 9317, 'L2': 2233, 'r0': 4, 'r1': 3}`
- `grow_then_L2_lt_L0`: fails=`2118862` ce=`{'n': 37, 'L0': 37, 'H': 86818724, 'L1': 9317, 'L2': 2233, 'r0': 4, 'r1': 3}`
- `eta_ge_L2_then_L2_lt_L0`: fails=`2169788` ce=`{'n': 37, 'L0': 37, 'H': 86818724, 'L1': 9317, 'L2': 2233, 'r0': 4, 'r1': 3}`
- `r_ge_4_then_L2_lt_L0`: fails=`973170` ce=`{'n': 37, 'L0': 37, 'H': 86818724, 'L1': 9317, 'L2': 2233, 'r0': 4, 'r1': 3}`
- `r_ge_4_then_next_r_lt_4`: fails=`150131` ce=`{'n': 193, 'L0': 122959442649427, 'H': 98657321694562501675205021287898285557337718595933234431125663931221095309446056660456573695238852474571940, 'L1': 314097630832457094601796592567466624850923021672186263, 'L2': 50959183530485503485198639535818032319035928338337423375592984269127, 'r0': 5, 'r1': 4}`
- `rho_gt_2_then_next_rho_lt_1`: fails=`1237616` ce=`{'n': 173, 'L0': 329, 'H': 32533545863179570755492129120411963721630316057459884067704058780, 'L1': 180370579261640036336071806107777, 'L2': 1941719144218166368455510841464890645, 'r0': 8, 'r1': 2}`
- `u_gt_1_then_v_lt_1`: fails=`1237620` ce=`{'n': 89, 'L0': 89, 'H': 24302, 'L1': 155, 'L2': 291, 'r0': 2, 'r1': 2}`

## Hold-out

- train: `{'excursions': 8186608, 'pairs': 3196186, 'sup_c': 28.832519530102534, 'sup_c2': 48.6546124129161, 'sup_rho': 2.3155909837573475e+148, 'sup_product': 6.125535690304958e+147, 'sup_u': 28.832519530102534, 'sup_v_given_u_gt_1': 28.832519530102534}`
- hold breaks: `{'broke_c': None, 'broke_c2': None, 'broke_rho': None, 'broke_product': None, 'broke_v_given_u': None}`

## Existing Lean (unchanged)

- `AboveAnchor`: `True`
- `EnvelopeState`: `True`
- `oe_block_contracts`: `True`
- `isolatedOddSurvival_bound`: `True`
- `power_bound_word`: `True`
- new Lean file: `False`

## Anti-overclaim

- global_termination: `False`
- global_divergence: `False`
- every_trajectory_contains_word: `False`
- parity_frequency_theorem: `False`
- finite_macro_transition_grammar: `False`
- average_formal_energy_decreases: `False`
- floating_point_verdict: `False`
- global_non_realizability: `False`
- A_w_empty_from_window: `False`
- density_theorem: `False`
- two_episode_descent_theorem: `False`
- compensation_theorem: `False`
- excursion_transfer_lean: `False`
- itinerary_language_reopen: `False`
- macro_event_reopen: `False`
- source_descent_reopen: `False`
- search_horizon_is_L: `False`

## Decision

**EXCURSION_TRANSFER_CLOSED**

Return B is the Q-source chain; every tested one-step, two-step, compensation, and weighted inequality has a counterexample; growth can follow growth; r-bin envelopes stay under the formal 3^r/2^{r+1} scale; no exact source recurrence.

