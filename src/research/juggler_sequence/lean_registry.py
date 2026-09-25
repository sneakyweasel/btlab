"""Juggler Lean module registry, layer order and source-inspection helpers.

Stable directory constants belong in lean_paths. Research registration
changes this module; numerical probes that only need directories do not import it.
"""
from __future__ import annotations

import re
from pathlib import Path

from research.juggler_sequence.lean_paths import (
    ENGINE_DIR,
    JUGGLER_BARREL,
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
)


PAPER_MODULES: tuple[str, ...] = (
    "Dynamics",
    "RootCells",
    "NumericBridge",
    "LogCells",
    "Iteration",
    "Termination",
    "Itinerary",
    "ItineraryStats",
    "Envelope",
    "Equality",
    "Defect",
    "GlobalDefect",
    "Preimages",
    "Certificates",
    "Progress",
    "Cycles",
    "LeftoverEval",
    "LeftoverPreimage",
    "LeftoverShort",
    "LeftoverFamilies",
    "O7EEEEGap",
    "EvenCountThree",
    "CycleRunForm",
    "SmallCycleCensus",
    "NormalizedDefect",
    "ExpansionSlack",
    "NearTightScale",
    "CycleFinance",
    "CycleFinanceLeftovers",
    "GapTransfer",
    "GapTransferWW",
    "RunSurvivorLattice",
    "WalkChargeItineraries",
    "OstrowskiSandwich",
    "OddCountMonotone",
    "RunTypePacking",
    "EvenCountEight",
    "DenjoyKoksma",
    "DenjoyKoksmaOrbit",
    "JumpVariation",
    "OstrowskiNumeration",
    "OstrowskiBlocks",
    "HugRotation",
    "HugChargeEnvelope",
    "RotationAverage",
    "FanLaw",
    "WalkTransport",
    "WalkChargeMax",
    "DefectFinance",
    "FinanceTransfer",
    "CubicBand",
    "CubicRotation",
    "CubicGrid",
    "CubicLogGrid",
    "CubicUpperCells",
    "CubicRounding",
    "CubicInterlacing",
    "CubicConsequences",
    "ReturnInduction",
    "ReturnCells",
    "FamilyChains",
    "CubicReturnHeight",
    "RemainderCarry",
    "CubicReturn",
    "CubicReturnStrip",
    "GuardResidueFamily",
    "ReturnWordLoss",
    "ReturnWordData",
    "ReturnWordBounds",
    "ReturnWordFactorization",
    "ReturnSeams",
    "ReturnRankedCycle",
    "CubicOrbitCharge",
    "CubicChargeMonotonicity",
    "ReturnQuotients",
    "ReturnCycleTransfers",
    "ReturnGapHeight",
    "ReturnTransferHeight",
    "ReturnTerminal",
    "ReturnOrbitStrips",
    "UpperSquareGap",
    "CollatzBridge",
)

LAYERS: dict[str, Path] = {
    "Dynamics": JUGGLER_DIR / "Dynamics.lean",
    "RootCells": JUGGLER_DIR / "RootCells.lean",
    "NumericBridge": JUGGLER_DIR / "NumericBridge.lean",
    "LogCells": JUGGLER_DIR / "LogCells.lean",
    "FateLandingWindow": JUGGLER_DIR / "FateLandingWindow.lean",
    "FateNumerics": JUGGLER_DIR / "FateNumerics.lean",
    "FateWindowCount": JUGGLER_DIR / "FateWindowCount.lean",
    "Iteration": JUGGLER_DIR / "Iteration.lean",
    "Termination": JUGGLER_DIR / "Termination.lean",
    "TerminationFloor257": JUGGLER_DIR / "TerminationFloor257.lean",
    "Itinerary": JUGGLER_DIR / "Itinerary.lean",
    "ItineraryStats": JUGGLER_DIR / "ItineraryStats.lean",
    "Envelope": JUGGLER_DIR / "Envelope.lean",
    "Corridor": JUGGLER_DIR / "Corridor.lean",
    "CubeCorridor": JUGGLER_DIR / "CubeCorridor.lean",
    "Equality": JUGGLER_DIR / "Equality.lean",
    "Defect": JUGGLER_DIR / "Defect.lean",
    "GlobalDefect": JUGGLER_DIR / "GlobalDefect.lean",
    "DefectLowerBound": JUGGLER_DIR / "DefectLowerBound.lean",
    "Preimages": JUGGLER_DIR / "Preimages.lean",
    "Collapse": JUGGLER_DIR / "Collapse.lean",
    "Drift": JUGGLER_DIR / "Drift.lean",
    "FirstPassage": JUGGLER_DIR / "FirstPassage.lean",
    "Certificates": JUGGLER_DIR / "Certificates.lean",
    "Progress": JUGGLER_DIR / "Progress.lean",
    "RateFreeDensity": JUGGLER_DIR / "RateFreeDensity.lean",
    "FateCylinderEnergy": JUGGLER_DIR / "FateCylinderEnergy.lean",
    "FirstInternalOO": JUGGLER_DIR / "FirstInternalOO.lean",
    "MinimumRelative": JUGGLER_DIR / "MinimumRelative.lean",
    "Minimal": JUGGLER_DIR / "Minimal.lean",
    "MinimalClosure": JUGGLER_DIR / "MinimalClosure.lean",
    "Scale": JUGGLER_DIR / "Scale.lean",
    "Residuals": JUGGLER_DIR / "Residuals.lean",
    "NormalizedDefect": JUGGLER_DIR / "NormalizedDefect.lean",
    "ExpansionBlocks": JUGGLER_DIR / "ExpansionBlocks.lean",
    "ExpansionSlack": JUGGLER_DIR / "ExpansionSlack.lean",
    "NearTightScale": JUGGLER_DIR / "NearTightScale.lean",
    "ExpandingGrammar": JUGGLER_DIR / "ExpandingGrammar.lean",
    "LandingParity": JUGGLER_DIR / "LandingParity.lean",
    "CycleCore": JUGGLER_DIR / "CycleCore.lean",
    "CycleObstructions": JUGGLER_DIR / "CycleObstructions.lean",
    "CycleExtrema": JUGGLER_DIR / "CycleExtrema.lean",
    "Cycles": JUGGLER_DIR / "Cycles.lean",
    "LeftoverEval": JUGGLER_DIR / "LeftoverEval.lean",
    "LeftoverPreimage": JUGGLER_DIR / "LeftoverPreimage.lean",
    "LeftoverShort": JUGGLER_DIR / "LeftoverShort.lean",
    "FirstETransportEval": JUGGLER_DIR / "FirstETransportEval.lean",
    "BunchedTight": JUGGLER_DIR / "BunchedTight.lean",
    "LeftoverFamilies": JUGGLER_DIR / "LeftoverFamilies.lean",
    "PrefixTwoEvenEval": JUGGLER_DIR / "PrefixTwoEvenEval.lean",
    "PrefixTwoEven": JUGGLER_DIR / "PrefixTwoEven.lean",
    "PrefixBunchedEval": JUGGLER_DIR / "PrefixBunchedEval.lean",
    "PrefixBunched": JUGGLER_DIR / "PrefixBunched.lean",
    "SmallCycleCensus": JUGGLER_DIR / "SmallCycleCensus.lean",
    "LengthEightCensus": JUGGLER_DIR / "LengthEightCensus.lean",
    "CycleDiophantine": JUGGLER_DIR / "CycleDiophantine.lean",
    "EvenCountThree": JUGGLER_DIR / "EvenCountThree.lean",
    "CycleRunForm": JUGGLER_DIR / "CycleRunForm.lean",
    "CycleMinObstruction": JUGGLER_DIR / "CycleMinObstruction.lean",
    "O7EEEEGap": JUGGLER_DIR / "O7EEEEGap.lean",
    "CycleMinFudge": JUGGLER_DIR / "CycleMinFudge.lean",
    "SequentialMordell": JUGGLER_DIR / "SequentialMordell.lean",
    "LandingValuation": JUGGLER_DIR / "LandingValuation.lean",
    "PreimageCylinders": JUGGLER_DIR / "PreimageCylinders.lean",
    "OddLandingSets": JUGGLER_DIR / "OddLandingSets.lean",
    "ItineraryLanguage": JUGGLER_DIR / "ItineraryLanguage.lean",
    "GapCells": JUGGLER_DIR / "GapCells.lean",
    "Escape": JUGGLER_DIR / "Escape.lean",
    "CycleFinance": JUGGLER_DIR / "CycleFinance.lean",
    "CycleFinanceLeftovers": JUGGLER_DIR / "CycleFinanceLeftovers.lean",
    "RunSurvivorLattice": JUGGLER_DIR / "RunSurvivorLattice.lean",
    "CycleHeightFinance": JUGGLER_DIR / "CycleHeightFinance.lean",
    "WalkChargeItineraries": JUGGLER_DIR / "WalkChargeItineraries.lean",
    "OstrowskiSandwich": JUGGLER_DIR / "OstrowskiSandwich.lean",
    "OddCountMonotone": JUGGLER_DIR / "OddCountMonotone.lean",
    "RunTypePacking": JUGGLER_DIR / "RunTypePacking.lean",
    "EvenCountEight": JUGGLER_DIR / "EvenCountEight.lean",
    "DenjoyKoksma": JUGGLER_DIR / "DenjoyKoksma.lean",
    "DenjoyKoksmaOrbit": JUGGLER_DIR / "DenjoyKoksmaOrbit.lean",
    "JumpVariation": JUGGLER_DIR / "JumpVariation.lean",
    "OstrowskiNumeration": JUGGLER_DIR / "OstrowskiNumeration.lean",
    "OstrowskiBlocks": JUGGLER_DIR / "OstrowskiBlocks.lean",
    "HugRotation": JUGGLER_DIR / "HugRotation.lean",
    "FanLaw": JUGGLER_DIR / "FanLaw.lean",
    "WalkTransport": JUGGLER_DIR / "WalkTransport.lean",
    "WalkChargeMax": JUGGLER_DIR / "WalkChargeMax.lean",
    "HugChargeEnvelope": JUGGLER_DIR / "HugChargeEnvelope.lean",
    "RotationAverage": JUGGLER_DIR / "RotationAverage.lean",
    "DefectFinance": JUGGLER_DIR / "DefectFinance.lean",
    "FinanceTransfer": JUGGLER_DIR / "FinanceTransfer.lean",
    "AboveAnchorWalk": JUGGLER_DIR / "AboveAnchorWalk.lean",
    "GapTransfer": JUGGLER_DIR / "GapTransfer.lean",
    "FunctionalGraph": JUGGLER_DIR / "FunctionalGraph.lean",
    "FateContagion": JUGGLER_DIR / "FateContagion.lean",
    "LogLogClock": JUGGLER_DIR / "LogLogClock.lean",
    "TowerAbsorption": JUGGLER_DIR / "TowerAbsorption.lean",
    "TiltedShare": JUGGLER_DIR / "TiltedShare.lean",
    "LiveCountWeight": JUGGLER_DIR / "LiveCountWeight.lean",
    "DepthOneMainTerm": JUGGLER_DIR / "DepthOneMainTerm.lean",
    "CycleRunAlphabet": JUGGLER_DIR / "CycleRunAlphabet.lean",
    "ParityComplexity": JUGGLER_DIR / "ParityComplexity.lean",
    "LocalizedKernel": JUGGLER_DIR / "LocalizedKernel.lean",
    "CubeFiber": JUGGLER_DIR / "CubeFiber.lean",
    "FateRecursion": JUGGLER_DIR / "FateRecursion.lean",
    "FateFirstLetter": JUGGLER_DIR / "FateFirstLetter.lean",
    "FateBlockLock": JUGGLER_DIR / "FateBlockLock.lean",
    "FateSweep": JUGGLER_DIR / "FateSweep.lean",
    "FateSweepMonotone": JUGGLER_DIR / "FateSweepMonotone.lean",
    "FateChernoff": JUGGLER_DIR / "FateChernoff.lean",
    "FatePressure": JUGGLER_DIR / "FatePressure.lean",
    "FateTaoReduction": JUGGLER_DIR / "FateTaoReduction.lean",
    "FateSeed": JUGGLER_DIR / "FateSeed.lean",
    "CubicBand": JUGGLER_DIR / "CubicBand.lean",
    "CubicRotation": JUGGLER_DIR / "CubicRotation.lean",
    "CubicGrid": JUGGLER_DIR / "CubicGrid.lean",
    "CubicLogGrid": JUGGLER_DIR / "CubicLogGrid.lean",
    "CubicUpperCells": JUGGLER_DIR / "CubicUpperCells.lean",
    "CubicRounding": JUGGLER_DIR / "CubicRounding.lean",
    "CubicInterlacing": JUGGLER_DIR / "CubicInterlacing.lean",
    "CubicConsequences": JUGGLER_DIR / "CubicConsequences.lean",
    "ReturnInduction": JUGGLER_DIR / "ReturnInduction.lean",
    "ReturnCells": JUGGLER_DIR / "ReturnCells.lean",
    "FamilyChains": JUGGLER_DIR / "FamilyChains.lean",
    "CubicReturnHeight": JUGGLER_DIR / "CubicReturnHeight.lean",
    "RemainderCarry": JUGGLER_DIR / "RemainderCarry.lean",
    "CubicReturn": JUGGLER_DIR / "CubicReturn.lean",
    "CubicReturnStrip": JUGGLER_DIR / "CubicReturnStrip.lean",
    "GuardResidueFamily": JUGGLER_DIR / "GuardResidueFamily.lean",
    "ReturnWordLoss": JUGGLER_DIR / "ReturnWordLoss.lean",
    "ReturnWordData": JUGGLER_DIR / "ReturnWordData.lean",
    "ReturnWordBounds": JUGGLER_DIR / "ReturnWordBounds.lean",
    "ReturnWordFactorization": JUGGLER_DIR / "ReturnWordFactorization.lean",
    "ReturnSeams": JUGGLER_DIR / "ReturnSeams.lean",
    "ReturnRankedCycle": JUGGLER_DIR / "ReturnRankedCycle.lean",
    "CubicOrbitCharge": JUGGLER_DIR / "CubicOrbitCharge.lean",
    "CubicChargeMonotonicity": JUGGLER_DIR / "CubicChargeMonotonicity.lean",
    "ReturnQuotients": JUGGLER_DIR / "ReturnQuotients.lean",
    "ReturnCycleTransfers": JUGGLER_DIR / "ReturnCycleTransfers.lean",
    "ReturnGapHeight": JUGGLER_DIR / "ReturnGapHeight.lean",
    "ReturnTransferHeight": JUGGLER_DIR / "ReturnTransferHeight.lean",
    "ReturnTerminal": JUGGLER_DIR / "ReturnTerminal.lean",
    "ReturnOrbitStrips": JUGGLER_DIR / "ReturnOrbitStrips.lean",
    "QuarticBand": JUGGLER_DIR / "QuarticBand.lean",
    "QuarticCells": JUGGLER_DIR / "QuarticCells.lean",
    "QuarticProjection": JUGGLER_DIR / "QuarticProjection.lean",
    "QuarticLossBudget": JUGGLER_DIR / "QuarticLossBudget.lean",
    "QuarticDefect": JUGGLER_DIR / "QuarticDefect.lean",
    "QuarticGapSeparation": JUGGLER_DIR / "QuarticGapSeparation.lean",
    "UpperSquareGap": JUGGLER_DIR / "UpperSquareGap.lean",
    "CubicRemainderVariation": JUGGLER_DIR / "CubicRemainderVariation.lean",
    "CubicConstraintFusion": JUGGLER_DIR / "CubicConstraintFusion.lean",
    "CubicCriticalLocation": JUGGLER_DIR / "CubicCriticalLocation.lean",
    "CriticalCostKernel": JUGGLER_DIR / "CriticalCostKernel.lean",
    "CubicRemainderAssembly": JUGGLER_DIR / "CubicRemainderAssembly.lean",
    "FateCylinderCorollary": JUGGLER_DIR / "FateCylinderCorollary.lean",
    "FateFiberParity": JUGGLER_DIR / "FateFiberParity.lean",
    "FateFiberLock": JUGGLER_DIR / "FateFiberLock.lean",
    "FateThinFibers": JUGGLER_DIR / "FateThinFibers.lean",
    "FateResonanceCount": JUGGLER_DIR / "FateResonanceCount.lean",
    "FatePoorTail": JUGGLER_DIR / "FatePoorTail.lean",
    "FateBlockAverage": JUGGLER_DIR / "FateBlockAverage.lean",
    "FateShareLaw": JUGGLER_DIR / "FateShareLaw.lean",
    "FateContagionBound": JUGGLER_DIR / "FateContagionBound.lean",
    "FateProduction": JUGGLER_DIR / "FateProduction.lean",
    "FateProductionWords": JUGGLER_DIR / "FateProductionWords.lean",
    "FatePoorProduction": JUGGLER_DIR / "FatePoorProduction.lean",
    "FateDyadicDensity": JUGGLER_DIR / "FateDyadicDensity.lean",
    "FateOneSided": JUGGLER_DIR / "FateOneSided.lean",
    "FateOneSidedCorollary": JUGGLER_DIR / "FateOneSidedCorollary.lean",
    "FatePressureCorollary": JUGGLER_DIR / "FatePressureCorollary.lean",
    "OddCubicPhase": JUGGLER_DIR / "OddCubicPhase.lean",
    "CubicInverseCell": JUGGLER_DIR / "CubicInverseCell.lean",
    "FateOneSidedAtoms": JUGGLER_DIR / "FateOneSidedAtoms.lean",
    "FateEnergyAtoms": JUGGLER_DIR / "FateEnergyAtoms.lean",
    "FateCollapse": JUGGLER_DIR / "FateCollapse.lean",
    "FateCertified": JUGGLER_DIR / "FateCertified.lean",
    "GapTransferWW": JUGGLER_DIR / "GapTransferWW.lean",
    "CollatzBridge": JUGGLER_DIR / "CollatzBridge.lean",
    "CollatzRational": JUGGLER_DIR / "CollatzRational.lean",
    "PolynomialDual": JUGGLER_DIR / "PolynomialDual.lean",
    "OddPredecessorTransport": JUGGLER_DIR / "OddPredecessorTransport.lean",
    "CollatzPadic": JUGGLER_DIR / "CollatzPadic.lean",
    "CodeMassTransport": JUGGLER_DIR / "CodeMassTransport.lean",
    "FateOOEEAssembly": JUGGLER_DIR / "FateOOEEAssembly.lean",
    "FateOEWeighted": JUGGLER_DIR / "FateOEWeighted.lean",
    "FateScaleAverage": JUGGLER_DIR / "FateScaleAverage.lean",
    "OOEECurvature": JUGGLER_DIR / "OOEECurvature.lean",
    "OOEECarryCells": JUGGLER_DIR / "OOEECarryCells.lean",
    "OOEEFourierModes": JUGGLER_DIR / "OOEEFourierModes.lean",
    "OOEECarryFourier": JUGGLER_DIR / "OOEECarryFourier.lean",
    "OOEEPhaseComparison": JUGGLER_DIR / "OOEEPhaseComparison.lean",
    "OOEESmoothModes": JUGGLER_DIR / "OOEESmoothModes.lean",
    "OOEEMixedModes": JUGGLER_DIR / "OOEEMixedModes.lean",
    "OOEERootPhase": JUGGLER_DIR / "OOEERootPhase.lean",
    "OOEESlowModes": JUGGLER_DIR / "OOEESlowModes.lean",
    "OOEEParity": JUGGLER_DIR / "OOEEParity.lean",
    "OOEEFibreGeometry": JUGGLER_DIR / "OOEEFibreGeometry.lean",
    "OOEEFibreParity": JUGGLER_DIR / "OOEEFibreParity.lean",
    "OOEEFibreResonance": JUGGLER_DIR / "OOEEFibreResonance.lean",
    "OOEEResonanceTail": JUGGLER_DIR / "OOEEResonanceTail.lean",
    "FateOOEEWeighted": JUGGLER_DIR / "FateOOEEWeighted.lean",
}

# Sources belonging to other targets or historical model interfaces. Keeping
# them explicit makes the disk inventory complete without implying that they
# belong to Paper A's ordered publication layers.
AUXILIARY_MODULES: dict[str, str] = {
    "PaperEModularReturn": "Paper E Theorem 4.1: exact floor construction and denominator growth; infinitude conditional on explicit BoxRecurrence",
    "PaperERecurrence": "Paper E Theorem 4.1: proved simultaneous-box recurrence and unconditional modular-return theorem",
    "PaperECorollaries": "Paper E Corollaries 4.2-4.3: exact sparse-start counts, fixed relative intervals, and prescribed even-run residues",
    "OOEEffectiveModes": "Effective OOE supplement: actual signed third/fifth derivatives, dyadic mode bound 32, and uniform all-length normalized bound 128",
    "OOEEscapeResidue": "Paper A Proposition E.7: exact even first image on t^8+a and no eventually periodic OO-guarded domain",
    "HugFlowImageGap": "Depth-two hug-flow gap: odd images separated by 3 floor(sqrt x), beating the (2/3)Y^(1/3) window with ratio 9/2",
    "CubicHiddenParity": "Cube-threshold block s^4 -> s^6 -> s^3 hides the odd internal state s^6; actual image s^9",
    "CycleMinOOOSquare": "Two odd steps from x >= n >= 3 reach n^2; (OOE)^k keeps the square cell exactly for k <= 5",
    "CycleMinEnvelopes": "Power envelopes along the post-L corridor: L, M = L OOE and the W5 chain cells",
    "OddPreimageTypes": "Odd one-step preimage cell classified by the least cube root: Types 0, 1 and 2",
    "OOECarrySubstitution": "OOE carry family: quotient floors d and D differ by 36r^2+1; floor(x^(9/8)) = z+1",
    "PaperBBarrierMass": "Paper B barrier: update mass, the fract(t beta) phase of the rise, and N_(d+1) = 2N_d - b_d M_d",
    "CycleMinSecondPostL": "Second post-L OOE on a cycle minimum for every continuation, the empty one being a length-17 cycle",
    "FatePressureAveraged": "Paper C Proposition 9.3 corollary at the averaged exponent 103/203",
    "FatePressureOOEE": "Paper C Section 9.2 corollaries at the OOEE threshold 3/8",
    "EscapeRate": "An escape rate above 3/8 excludes divergent orbits",
    "FateOOOEEAssembly": "Four-production assembly: an OOOEE production at 1/30 gives contagion 2/3 and thresholds 1/3",
    "FateDepthFiveAssembly": "Five-production assembly: both depth-five productions at 1/28 give contagion 37/50 and thresholds 13/50",
    "SubBlockAveraging": "Lemma E9 core: a poor fibre has bad sub-blocks of total size at least (3/10) eta H",
    "DepthFiveFibreGeometry": "Exact OOOEE and OOEOE target fibres: endpoints within 4 of t^(32/27), about (16/27) t^(5/27) candidates",
    "FateDepthFiveWeighted": "Bounded count-poor tails for OOOEE and OOEOE give both depth-five productions at 1/28 and contagion 37/50",
    "OOEEffectiveReturn": "Paper E Theorem 4.4: exact floor-residue count, both uniform errors, positive count and bounded actual OOE modular witness",
    "PaperECompletion": "Paper E: series identification, frequency and exponent statements, direct stopping-word sums, and finite complete prefix trees",
    "CollatzMoments": "Paper B/C word-moment bridge: coefficient shift and complete first-descent stopping counterexample",
    "BranchFreeze": "Paper B review target",
    "MasterIdentity": "Paper B review target",
    "MeanValues": "Paper B review target",
    "MonomialSplitting": "Paper B review target",
    "PaperBAssembly": "Paper B review target",
    "PaperBCertificates": "Paper B Lemma 5.1: minimal certificates through length five",
    "PaperBFiveStepDensity": "Paper B Theorems 5.2-5.4: the certificate count assembly",
    "PaperBSingleFloor": "Paper B Theorem 3.1: exact bridge and one dyadic second-derivative block",
    "PaperBSingleFloorBound": "Paper B Theorem 3.1: S_O(N) = O(N^(5/6)) and both counts, via Erdos-Turan with main term N/H",
    "PaperBCarryExpansion": "Paper B Lemma 4.3, bound (4.3): the near-integer sum of E_R(n^(3/2)) over odd n in an interval",
    "PaperBSawtoothExpansion": "Paper B Lemma 4.3, first assertion: b = b_R + O(E_R) for the truncated sawtooth series, including at integers",
    "PaperBShiftAverage": "Paper B Proposition 7.4: the shift-averaged mean square (7.3) and its exceptional set of shifts",
    "PaperBOEThirdLetter": "Paper B Proposition 3.2: #word_3 = w is N/8 + O(N^(5/6) log N) for w = OEE, OEO, via the two-dimensional Erdos-Turan inequality",
    "PaperBCertificateLengths": "Paper B Lemma 5.1 for every length: the odd-count window",
    "PaperBCertificateRecursion": "Paper B: survivors and minimal certificates, one recursion",
    "BeattyPhaseTransfer": "Beatty phase coordinates, survivor jump cancellation, summable jump profiles, and conditional moving-kernel transfer",
    "BeattyRenewalLimit": "Renewal coefficient decay and moving-phase limit with a proved near/far convolution split",
    "BeattyRenewalSeries": "Formal exponential recurrence, summability, and analytic phase limit for renewal coefficients",
    "BeattySurvivorProfile": "Explicit survivor profile and conditional MeanderShape from the counting identity and terminal asymptotic",
    "BeattySlopeWords": "Actual binary survivor and first-passage counts at real boundaries, exact one-step partition and crossing-edge location",
    "BeattySlopeCounting": "Classical weighted positive-partial-sum recurrence for actual word counts at every irrational real boundary",
    "BeattySlopeRenewal": "Exact weighted renewal exponential, conditional analytic transfer, and a subcritical tilt for every boundary between zero and one",
    "BeattySlopeBinomial": "Finite tilted binomial tails with a uniform one-half geometric majorant and factor-two first-term comparison at every boundary in (0,1)",
    "BeattySlopeEndpointAsymptotic": "Tilted Stirling endpoint phase for every real boundary in (0,1) and unconditional weighted survivor phase at every irrational boundary",
    "BeattySlopeCriticalMass": "Finite critical mass and centered-moment bookkeeping, zero critical survival mass and total first-passage probability one at every irrational boundary in (0,1)",
    "BeattySlopeSeries": "Exact Beatty reindexing of critical probabilities and total positive-index jump mass beta/(1-beta) for every irrational boundary in (0,1)",
    "BeattySlopeIdentification": "Exact identification of the tilted survivor transfer with the strict Beatty jump profile at every irrational boundary in (0,1)",
    "BeattySlopeAsymptotic": "Original integer first-passage phase asymptotic in both binomial normalizations for every irrational slope alpha greater than one",
    "BeattySlopeSpecialization": "Exact finite-set identification with logarithmic certificate counts and independent boundary irrationality",
    "BeattySlopeProfileSpecialization": "Exact logarithmic specialization of crossing indices, phases, critical weights and strict profile",
    "BeattyCounting": "Unconditional integer survivor recurrence and exact positive-partial-sum exponential identity",
    "BeattyBinomialBounds": "Coarse terminal binomial bounds and unconditional sharp three-halves order of actual survivor counts",
    "BeattyEndpointAsymptotic": "Unconditional finer terminal and survivor phase asymptotics with exact fractional-part corrections",
    "BeattyCertificateMass": "Critical first-passage probability one from finite first moments and survivor decay",
    "BeattyCertificateSeries": "Actual Beatty certificate jump weights, exact total mass, positivity and one-sided traces",
    "BeattyCertificateIdentification": "Exact identification of the transferred survivor profile with the certificate jump series",
    "BeattyCertificateAsymptotic": "Unconditional original binomial-normalized certificate asymptotic with additive o(1) error",
    "BeattyProfileGeometry": "Exact gap complement, null perfect range closure, and recurrent sampling of cumulative jump profiles",
    "BeattySlopeCluster": "Complete actual-count cluster set for every irrational slope: compact perfect null set, exact gaps and eventual avoidance",
    "BeattyCertificateCluster": "Complete certificate accumulation set: compact perfect null geometry, exact gaps and eventual interior-gap avoidance",
    "BeattyWeakConvergence": "Almost-everywhere continuous mapping and vanishing-error transfer for empirical probability laws",
    "BeattyRotation": "Recurrence and uniform empirical distribution of every irrational real rotation",
    "BeattyPhaseEquidistribution": "Irrational Fourier cancellation and unconditional uniform empirical distribution of exact certificate phases",
    "BeattyCertificateDistribution": "Singular continuous empirical certificate law, continuous distribution function and exact phase thresholds",
    "BeattySlopeDistribution": "Singular continuous empirical law and exact threshold frequencies for actual first-passage ratios at every irrational slope",
    "BeattySlopeWeights": "Sharp three-halves gap asymptotic and global two-sided bounds at every irrational boundary",
    "BeattySlopeGapCounting": "Exact gap-counting asymptotic and phase moment throughout the irrational slope family",
    "BeattySlopeCantor": "Actual tube formula, cube-root bounds and Minkowski dimension two thirds for every irrational slope",
    "BeattySlopeContent": "Exact positive Minkowski content as a two-thirds moment for the whole irrational family",
    "BeattySlopeLocalCounting": "Spatially localized gap-counting asymptotic at every irrational slope",
    "BeattySlopeGeometricLaw": "Explicit local content and geometric probability as two-thirds reweightings of the family empirical law",
    "BeattySlopeLocalContent": "Weak limits of rescaled metric tube measures and uniform tube sampling for every irrational slope",
    "BeattySlopeHausdorff": "Finite two-thirds Hausdorff measure for every irrational slope and Hausdorff lower bounds from explicit phase-hitting or Diophantine premises",
    "BeattySlopeGammaAmplitude": "Exact Gamma-normalized first-passage amplitude q^delta F(delta) for the actual counts at every irrational boundary",
    "BeattySlopeGammaLaw": "Absolutely continuous Gamma-normalized empirical law, mutually singular with the binomial law, for every irrational slope",
    "BeattySlopeGammaDensity": "Explicit density series, occupation identity and logarithmic normalization of the family Gamma law",
    "BeattySlopeGammaMoments": "Positive envelope and every real-power moment series of the family Gamma law",
    "BeattySlopeGammaSupport": "Interval support, full Gamma-count cluster set, strict CDF and lower-semicontinuous density for every irrational slope",
    "BeattySlopeGammaBlowup": "Dense null G-delta blowup set and local essential unboundedness of the family Gamma density",
    "BeattySlopeGammaConcentration": "Cube-root concentration, 1/3-Hoelder CDF and weak three-halves density tails for every irrational slope",
    "BeattySlopeGammaLp": "Family Gamma density in L^p for 1<=p<3/2",
    "BeattySlopeGammaCDF": "Family Gamma CDF is nowhere locally Lipschitz in the support interior",
    "BeattySlopeGammaHausdorff": "Infinite-density set of the family Gamma law has Hausdorff dimension at most two thirds",
    "BeattyJumpCover": "Generic finite cut covers of a jump-profile range, gap masses and a Hausdorff-zero criterion",
    "BeattySlopeLiouville": "Hausdorff dimension zero of the actual cluster set at every Liouville slope, by exact rotation chains",
    "BeattySlopeGammaContinuity": "Weak continuity of the Gamma-normalized laws in the slope at irrational slopes",
    "BeattySlopeDiophantineDim": "Critical two-thirds Hausdorff measure is positive exactly at badly approximable slopes; Hausdorff dimension bounded by the irrationality exponent",
    "BeattySlopeRationalMass": "Exact critical first-passage mass and total jump weight at every boundary in (0,1), rational included",
    "BeattySlopeRationalLimit": "One-sided slope limits at rational slopes: l1 weights and convergence of the laws to uniform laws on b atoms",
    "BeattySlopeWeakCounting": "Weak positive-partial-sum recurrence for actual survivor counts at every real boundary",
    "BeattySlopeWeakPhase": "Weak tilted endpoint and survivor phase limits at every boundary in (0,1), rational included",
    "BeattySlopeWeakIdentification": "Right-trace profile identification and the phase theorem for actual ratios at every boundary in (0,1)",
    "BeattySlopeGlobalLaw": "Convergence of the empirical law of actual first-passage ratios for every real slope above one",
    "BeattySlopeLawContinuity": "Slope map of the limit laws: right-continuous at every slope, continuous exactly at irrational slopes, explicit jumps at rationals",
    "BeattySlopeExactDim": "Sharp Hausdorff lower bound 2/(2+tau) from many orbit hits per interval, exceeding the Denjoy-set value 2/(3 nu) for Diophantine class above one",
    "BeattySlopeIrrExp": "Hausdorff dimension two-thirds exactly when the irrationality exponent is two, including the logarithmic slope",
    "BeattySlopeRegularDim": "Exact Hausdorff dimension 2/(2+nu) for regular slopes via multi-level cell covers",
    "BeattySlopeConvergents": "Hand-built continued fractions, explicit regular slopes of every Diophantine class and the full Hausdorff dimension spectrum [0,2/3]",
    "BeattySlopeContinuity": "Local constancy of actual counts in the boundary, l1 continuity of jump weights, weak continuity of the laws and continuity of the Minkowski content at irrational slopes",
    "BeattySlopeArithmetic": "Hausdorff dimension two-thirds for almost every slope and positive finite two-thirds measure for every quadratic irrational slope",
    "BeattyCertificateWeights": "Moving phase asymptotic and uniform two-sided three-halves bounds for actual certificate gap weights",
    "BeattyGammaNormalization": "Uniform Gamma interpolation for arbitrary moving fractional parts from log-convexity",
    "BeattyFirstPassageAmplitude": "Exact BGL Gamma normalization and explicit periodic amplitude for original integer certificate counts",
    "BeattyAmplitudeRegularity": "Null-image derivative criterion and absolute continuity of real pushforward measures without global injectivity",
    "BeattyPassageDistribution": "Absolutely continuous empirical law of the Gamma-normalized first-passage counts and singular contrast with the original law",
    "BeattyFiniteOccupation": "Finite cumulative-jump calculus with exact endpoint and jump terms",
    "BeattyOccupationPrimitive": "Logarithmic occupation primitive, uniform increment bounds and the exact finite-cutoff identity",
    "BeattyOccupationLimit": "Summable dense-jump occupation identity from dominated finite cutoffs and endpoint mass balance",
    "BeattyOccupationMeasure": "Identification of an occupation measure with overlapping logarithmic interval measures and their density series",
    "BeattyPassageDensity": "Explicit density, unit integral, almost-everywhere finiteness and logarithmic normalization for the actual Gamma-normalized law",
    "BeattyPassageMoments": "Positive compact envelope and exact convergent series for every nonzero real-power moment of the amplitude law",
    "BeattyAmplitudeRange": "Downward intermediate values and interval ranges for left-continuous closed paths with upward jumps",
    "BeattyAmplitudeSupport": "Pushforward support and recurrent-sample cluster sets from one-sided continuity",
    "BeattyOccupationSupport": "Exact support of overlapping logarithmic jump-interval measures",
    "BeattyPassageSupport": "Concrete Gamma-law interval support, original-count cluster set and strictly increasing CDF",
    "BeattyPassageDensityTopology": "Lower semicontinuity and the infinite-overlap criterion for the explicit density",
    "BeattyPassageDensityBlowup": "Dense null G-delta of density blowup and version-independent local essential unboundedness",
    "BeattyGapVolume": "Exact metric neighbourhood volume of an interval complement from its disjoint exhaustive gaps",
    "BeattyGapDecay": "Integral-test tail bound and cube-root truncated-sum bounds for three-halves gap lengths",
    "BeattyCertificateCantor": "Exact certificate tube formula, positive finite cube-root volume bounds and Minkowski dimension two thirds",
    "BeattyPassageConcentration": "Measurable-set cube-root concentration, global Holder CDF and weak three-halves density tails",
    "BeattyPassageLp": "Subcritical density power integrability and Lp membership below three-halves",
    "BeattyOverlapEnergy": "Exact ordered pair-overlap criterion for Gamma-density square integrability; finiteness remains open",
    "BeattyPassageCDF": "Failure of local Lipschitz regularity of the Gamma CDF throughout its support interior",
    "BeattyDensityHausdorff": "Exact infinite-density set identification and unconditional two-thirds Hausdorff dimension upper bound",
    "BeattyPhaseCounting": "Moving index cutoffs for equidistributed monotone phase profiles and vanishing perturbations",
    "BeattyGapCounting": "Exact two-thirds gap-counting asymptotic for the original certificate weights",
    "BeattyGapContent": "Layer-cake identity and exact integration of the two-thirds gap-counting asymptotic",
    "BeattyCertificateContent": "Positive exact Minkowski content and its identification with the singular law's two-thirds moment",
    "BeattyLocalCounting": "Nonnegative moving cutoffs and certificate gap-counting asymptotics localized at every spatial threshold",
    "BeattyLocalVolume": "Uniform spatial-tail error bound between actual metric tubes and their truncated gaps marked by left endpoints",
    "BeattyTailConvergence": "Weak convergence of real probability and finite measures from their spatial tails and total masses",
    "BeattyGeometricLaw": "Explicit local geometric content and its normalized two-thirds-weighted certificate probability law",
    "BeattyCertificateLocalContent": "Weak convergence of actual rescaled tube measures and uniform tube probabilities to the geometric certificate law",
    "BeattyHausdorffUpper": "Finite two-thirds Hausdorff measure and unconditional Hausdorff dimension upper bound from actual certificate tube volumes",
    "BeattyPhaseHolder": "Explicit phase hitting bounds imply certificate CDF Holder regularity, positive Hausdorff measure and conditional dimension lower bounds",
    "BeattyRotationCover": "Reduced rational grids cover positive rotation orbits with explicit endpoint and inverse-square error bounds",
    "BeattyDiophantineHitting": "Dirichlet approximation turns uniform Diophantine lower bounds into phase hitting with the same exponent",
    "BeattyDiophantineGeometry": "Explicit Diophantine premises give certificate Hausdorff lower bounds and exact dimension from exponents approaching one",
    "PaperBLevelWindow": "The empty-window theorem at every level, not only Paper B's",
    "PaperBJumpTransposition": "Paper B: one barrier transposition costs the barrier mass",
    "CollatzBridgeLab": "Laboratory extensions of the Collatz bridge: the minimal-certificate count as a residue count (Paper B recursion) and the -17 cycle word inside CycleMinShape (IdealCycleMin)",
    "PaperBChainRule": "Paper B review target",
    "PaperBAmplitudeCocycle": "Paper B profile: the amplitude cocycle",
    "PaperBDensity": "Paper B: Hypothesis FD to density one, conditionally",
    "PaperBChernoff": "Paper B estimate: the Chernoff factor is below one",
    "PaperBMarkov": "Paper B estimate: the exponential Markov step",
    "PaperBSurvivorDecay": "Paper B Theorem 6.1 count: survivor density decays, conditional density one",
    "PaperBSurvivorAsymptotic": "Paper B exact-rate skeleton: meander shape and sharpness up to d^(3/2)",
    "PaperBBackwardWord": "Paper B barrier word: the arc form",
    "PaperBBarrierStep": "Paper B barrier word: one update step",
    "PaperBPaperCBridge": "Paper B/C bridge: one rate function",
    "PaperBSlopeRate": "Paper B rate: double root and slope derivative",
    "PaperBSturmianBarrier": "Paper B barrier word: uniformity across slopes",
    "PaperBTailSpectrum": "Paper B tail: the double root and the gap law",
    "PaperBThreshold": "Paper B review target",
    "PaperBTilt": "Paper B tilt: the psi reduction",
    "PaperBWeightGap": "Paper B spectrum: no weight restores the gap",
    "PeriodFamily": "Cycle period family arithmetic",
    "ThresholdCertificate": "Paper B review target",
    "DepthFourFive": "Independent historical parity support",
    "DividedBounds": "Independent historical parity support",
    "CyclePosition": "Laboratory ideal-cycle model",
    "IdealCycleMin": "Laboratory ideal-cycle model",
    "IdealLollipop": "Laboratory ideal-cycle model",
    "InverseBranches": "Laboratory inverse-branch interface",
    "Seam": "Laboratory cycle-seam interface",
}

DYNAMICS = LAYERS["Dynamics"]
ITERATION = LAYERS["Iteration"]
TERMINATION = LAYERS["Termination"]
ITINERARY = LAYERS["Itinerary"]
WORD_STATS = LAYERS["ItineraryStats"]
ENVELOPE = LAYERS["Envelope"]
EQUALITY = LAYERS["Equality"]
DEFECT = LAYERS["Defect"]
GLOBAL_DEFECT = LAYERS["GlobalDefect"]
DEFECT_LOWER_BOUND = LAYERS["DefectLowerBound"]
PREIMAGES = LAYERS["Preimages"]
CELLS = PREIMAGES
COLLAPSE = LAYERS["Collapse"]
DRIFT = LAYERS["Drift"]
FIRST_PASSAGE = LAYERS["FirstPassage"]
CERTIFICATES = LAYERS["Certificates"]
PROGRESS = LAYERS["Progress"]
RATE_FREE_DENSITY = LAYERS["RateFreeDensity"]
MINIMAL = LAYERS["Minimal"]
MINIMAL_CLOSURE = LAYERS["MinimalClosure"]
SCALE = LAYERS["Scale"]
MINIMUM_RELATIVE = LAYERS["MinimumRelative"]
RESIDUALS = LAYERS["Residuals"]
NORMALIZED_DEFECT = LAYERS["NormalizedDefect"]
EXPANSION_BLOCKS = LAYERS["ExpansionBlocks"]
EXPANSION_SLACK = LAYERS["ExpansionSlack"]
NEAR_TIGHT_SCALE = LAYERS["NearTightScale"]
EXPANDING_GRAMMAR = LAYERS["ExpandingGrammar"]
LANDING_PARITY = LAYERS["LandingParity"]
CYCLE_CORE = LAYERS["CycleCore"]
CYCLE_OBSTRUCTIONS = LAYERS["CycleObstructions"]
CYCLE_EXTREMA = LAYERS["CycleExtrema"]
CYCLES_BARREL = LAYERS["Cycles"]


class _CycleKernel:
    """`Cycles.lean` is a barrel. Probes that read `CYCLES` still see the kernel."""

    def read_text(self, encoding: str = "utf-8") -> str:
        return cycle_kernel_text()

    def is_file(self) -> bool:
        return (
            CYCLE_CORE.is_file()
            and CYCLE_OBSTRUCTIONS.is_file()
            and CYCLE_EXTREMA.is_file()
        )


CYCLES = _CycleKernel()
LEFTOVER_EVAL = LAYERS["LeftoverEval"]
LEFTOVER_PREIMAGE = LAYERS["LeftoverPreimage"]
LEFTOVER_CELL = LEFTOVER_PREIMAGE
LEFTOVER_SHORT = LAYERS["LeftoverShort"]
LEFTOVER_FAMILIES = LAYERS["LeftoverFamilies"]
PREFIX_TWO_EVEN_EVAL = LAYERS["PrefixTwoEvenEval"]
PREFIX_TWO_EVEN = LAYERS["PrefixTwoEven"]
PREFIX_BUNCHED_EVAL = LAYERS["PrefixBunchedEval"]
PREFIX_BUNCHED = LAYERS["PrefixBunched"]
# Historical names: leftover proofs now live in Short / Families.
LEFTOVER_CYCLES = LEFTOVER_SHORT
LEFTOVER_TWO_EVEN = LEFTOVER_FAMILIES
FIRST_E_TRANSPORT_EVAL = LAYERS["FirstETransportEval"]
FIRST_E_TRANSPORT = LEFTOVER_FAMILIES
GAPPED_CYCLE_WORD = LEFTOVER_FAMILIES
BUNCHED_EEE = LEFTOVER_FAMILIES
# Historical names: the isolated Bunched*Eval tables were merged
# into LeftoverEval.lean (one maxHeartbeats header, same theorems).
BUNCHED_EOEE_EVAL = LEFTOVER_EVAL
BUNCHED_EOEE = LEFTOVER_FAMILIES
BUNCHED_EOOEE_EVAL = LEFTOVER_EVAL
BUNCHED_EOOEE = LEFTOVER_FAMILIES
BUNCHED_EEOE_EVAL = LEFTOVER_EVAL
BUNCHED_EEOE = LEFTOVER_FAMILIES
BUNCHED_EOEOE_EVAL = LEFTOVER_EVAL
BUNCHED_EOEOE = LEFTOVER_FAMILIES
BUNCHED_EOOOEE_EVAL = LEFTOVER_EVAL
BUNCHED_TIGHT = LAYERS["BunchedTight"]
BUNCHED_EOOOEE = LEFTOVER_FAMILIES
BUNCHED_EOOEOE_EVAL = LEFTOVER_EVAL
BUNCHED_EOOEOE = LEFTOVER_FAMILIES
SMALL_CYCLE_CENSUS = LAYERS["SmallCycleCensus"]
LENGTH_EIGHT_CENSUS = LAYERS["LengthEightCensus"]
EVEN_COUNT_THREE = LAYERS["EvenCountThree"]
CYCLEMIN_OBSTRUCTION = LAYERS["CycleMinObstruction"]
FIRST_INTERNAL_OO = LAYERS["FirstInternalOO"]
O7EEEE_GAP = LAYERS["O7EEEEGap"]
CYCLEMIN_FUDGE = LAYERS["CycleMinFudge"]
CYCLE_DIOPHANTINE = LAYERS["CycleDiophantine"]
SEQUENTIAL_MORDELL = LAYERS["SequentialMordell"]
LANDING_VALUATION = LAYERS["LandingValuation"]
PREIMAGE_CYLINDERS = LAYERS["PreimageCylinders"]
ODD_LANDING_SETS = LAYERS["OddLandingSets"]
WORD_LANGUAGE = LAYERS["ItineraryLanguage"]
GAP_CELLS = LAYERS["GapCells"]
ESCAPE = LAYERS["Escape"]
CYCLE_FINANCE = LAYERS["CycleFinance"]
CYCLE_FINANCE_LEFTOVERS = LAYERS["CycleFinanceLeftovers"]
RUN_SURVIVOR_LATTICE = LAYERS["RunSurvivorLattice"]
CYCLE_HEIGHT_FINANCE = LAYERS["CycleHeightFinance"]
WALK_CHARGE_WORDS = LAYERS["WalkChargeItineraries"]
WALK_TRANSPORT = LAYERS["WalkTransport"]
ABOVE_ANCHOR_WALK = LAYERS["AboveAnchorWalk"]
# Historical name: the open-flight transport envelope was re-rooted on
# AboveAnchor and merged into WalkTransport.lean.
FLIGHT_ENVELOPE = LAYERS["WalkTransport"]

DELETED_ENGINE = (
    ENGINE_DIR / "FloorPower.lean",
    ENGINE_DIR / "Progress.lean",
    ENGINE_DIR / "MinimalNonTerm.lean",
    ENGINE_DIR / "RepeatedOE.lean",
    ENGINE_DIR / "OddRunFinancing.lean",
    ENGINE_DIR / "OddOddFrontier.lean",
    ENGINE_DIR / "ResidualChain.lean",
    ENGINE_DIR / "ResidualPath.lean",
    ENGINE_DIR / "RepeatedBlock.lean",
    ENGINE_DIR / "CycleItinerary.lean",
    ENGINE_DIR / "CycleDiophantine.lean",
)


def juggler_sources(*, exclude: tuple[str, ...] = ()) -> list[Path]:
    skip = set(exclude)
    return [
        JUGGLER_BARREL,
        JUGGLER_PAPER_BARREL,
        *[path for name, path in LAYERS.items() if name not in skip],
    ]


def juggler_text(*, exclude: tuple[str, ...] = ()) -> str:
    return "\n".join(
        path.read_text(encoding="utf-8") for path in juggler_sources(exclude=exclude)
    )


def pre_finance_text() -> str:
    """Laboratory corpus without CycleFinance.lean.

    Older leftover/census probes treat length-9/10 absence as “this
    branch did not add a census.” Finance later proved those lengths
    by a different inequality; they must not flip those probes.
    """
    return juggler_text(
        exclude=("CycleFinance", "CycleFinanceLeftovers", "CycleHeightFinance")
    )


def cycle_kernel_text() -> str:
    """`Cycles.lean` is a barrel. Kernel declarations live in Core + named words + Extrema."""
    return (
        CYCLE_CORE.read_text(encoding="utf-8")
        + "\n"
        + CYCLE_OBSTRUCTIONS.read_text(encoding="utf-8")
        + "\n"
        + CYCLE_EXTREMA.read_text(encoding="utf-8")
    )


def engine_juggler_gone() -> bool:
    return not any(path.is_file() for path in DELETED_ENGINE)


def engine_floor_text() -> str:
    """Body of the deleted Engine FloorPower file. Empty after the rewrite."""
    path = ENGINE_DIR / "FloorPower.lean"
    return path.read_text(encoding="utf-8") if path.is_file() else ""


def has_named(text: str, name: str) -> bool:
    return any(
        f"{kind} {name}" in text
        for kind in ("theorem", "def", "inductive", "abbrev", "structure")
    )


def declares_name(text: str, name: str, kinds: tuple[str, ...] = ("def", "structure")) -> bool:
    """Does ``text`` declare exactly ``name`` under one of ``kinds``?

    ``has_named`` matches on a bare substring, so ``"def Energy"`` also
    fires on ``def EnergyBound``. A forbidden-engine guard must not be
    tripped by an unrelated declaration that merely shares a prefix, so
    the name has to end where the match ends.
    """
    pattern = rf"\b(?:{'|'.join(re.escape(kind) for kind in kinds)})\s+{re.escape(name)}\b"
    return re.search(pattern, text) is not None
