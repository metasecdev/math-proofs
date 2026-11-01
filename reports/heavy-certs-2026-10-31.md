# Heavy certificates (`BBPHeavyCerts`) — build and axiom report, 2026-10-31

**Result: PASS.** `lake build` (default target) and `lake build BBPHeavyCerts` completed with 0 errors and no `sorry`.
All 135 `#print axioms` results list only `propext`, `Classical.choice`, `Quot.sound`
(`scripts/check_axioms.py` exit 0; it also scanned the Lean sources for `sorry`/`admit`/`native_decide`/`axiom`/`implemented_by`/`extern`: none).

## Machine
- MacBook Pro (MacBookPro16,1), Intel Core i9-9980HK @ 2.40 GHz, 8 cores / 16 threads, 64 GB RAM, macOS 26.6.2 (25G83), x86_64
- Lean 4.29.0-rc8 (`leanprover/lean4:v4.29.0-rc8`), Mathlib @ 816ff4582a01b10567d1d4ecb10be7c4ff92aab4 (`lake exe cache get`)

## Commits
- Full build (Mathlib cache, default target, all heavy certificates): `4a6b74cc1f54e3b4cda58d469fa71eedb9391f0b`.
- Fast-forwarded to `d8e418e2a5d6fee7e4c43297ca8280c2e538e51b` (main after #6–#8: comment/docs/paper changes only; no heavy-certificate source, `BBPFastGuard`, lakefile, manifest or toolchain change), incrementally rebuilt both targets (rc 0), and ran the axiom reports there.

## Timing (America/New_York, 2026-10-31)
| step | time |
|---|---|
| `lake exe cache get` | 86 s |
| `lake build` (default target, from cache) | 949 s (15 m 49 s) |
| `lake build BBPHeavyCerts` | ≈ 37 m of build time (sum of lake runs 2205 s), 21:10 → 22:04 wall clock |
| incremental rebuild at `d8e418e` (both targets) | 251 s |

The first heavy attempt (plain `lake build BBPHeavyCerts`, 16 parallel Lean processes) was aborted after 11 min because of
memory thrashing (swap full). The certificate modules were then built in batches (`lake build <modules…>`, 8 at a time, then 4 at a time
for `BBPFastCerts10000Part62–82`), the three `BBPFastCerts{3099,5899,8299}` modules, and finally `lake build BBPHeavyCerts`
(“Build completed successfully (8372 jobs)”). Lake resumes incrementally, so nothing was compiled twice except the aborted batch.

**Peak memory:** largest single Lean process ≈ 16 GB (15.9 GB RSS sampled for `BBPFastCerts10000Part82`; `/usr/bin/time -l` max RSS 16.7 GB); typical certificate part 4–10 GB.
Recommendation: on a 64 GB machine build with ≤ 4 certificate modules at once.

## Theorems covered
`#print axioms` was run on every public theorem in the 135 heavy-only modules of the `BBPHeavyCerts` closure
(`BBPFastCerts*`, `BBPFastCertsT8300to10000*`, `BBPDigitsUnconditionalExt{3099,5899,8299,10000}`), plus `Thoughts/AxiomsHeavy.lean`.
The 126 `private` chunk lemmas (`fast_chunk_*`, each a `decide +kernel` call) are not nameable from outside their files; they are covered
transitively by the public range theorems that use them.

Headline results:
- `FinitistProved.BBPSpigotDigitCorrect_of_le_3099_unconditional`: [propext, Classical.choice, Quot.sound]
- `FinitistProved.BBPSpigotDigitCorrect_of_le_5899_unconditional`: [propext, Classical.choice, Quot.sound]
- `FinitistProved.BBPSpigotDigitCorrect_of_le_8299_unconditional`: [propext, Classical.choice, Quot.sound]
- `FinitistProved.BBPSpigotDigitCorrect_of_le_10000_unconditional`: [propext, Classical.choice, Quot.sound]
- `FinitistProved.bbpGuardAgrees_of_lt_10001`: [propext, Classical.choice, Quot.sound]

Commands:
```
lake build BBPHeavyCerts
lake env lean Thoughts/AxiomsHeavy.lean > axioms-heavy.log
lake env lean HeavyAxiomReport.lean > axioms-heavy-all.log   # generated: imports all 135 modules, #print axioms on every public theorem
python3 scripts/check_axioms.py axioms-heavy.log axioms-heavy-all.log build_heavy.log build_heavy_main.log
```

## Axiom output (135 declarations)
| declaration | axioms |
|---|---|
| `FinitistProved.BBPSpigotDigitCorrect_of_le_10000_unconditional` | propext, Classical.choice, Quot.sound |
| `FinitistProved.BBPSpigotDigitCorrect_of_le_3099_unconditional` | propext, Classical.choice, Quot.sound |
| `FinitistProved.BBPSpigotDigitCorrect_of_le_5899_unconditional` | propext, Classical.choice, Quot.sound |
| `FinitistProved.BBPSpigotDigitCorrect_of_le_8299_unconditional` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_Ico_8300_10001` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_of_lt_10001` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_of_lt_3100` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_of_lt_5900` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_of_lt_8300` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_0_100` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_1000_1100` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_100_200` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_1100_1200` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_1200_1300` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_1300_1400` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_1400_1500` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_1500_1600` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_1600_1700` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_1700_1800` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_1800_1900` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_1900_2000` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_2000_2100` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_200_300` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_2100_2200` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_2200_2300` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_2300_2400` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_2400_2500` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_2500_2600` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_2600_2700` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_2700_2800` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_2800_2900` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_2900_3000` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_3000_3100` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_300_400` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_3100_3200` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_3200_3300` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_3300_3400` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_3400_3500` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_3500_3600` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_3600_3700` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_3700_3800` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_3800_3900` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_3900_4000` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_4000_4100` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_400_500` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_4100_4200` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_4200_4300` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_4300_4400` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_4400_4500` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_4500_4600` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_4600_4700` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_4700_4800` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_4800_4900` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_4900_5000` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_5000_5100` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_500_600` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_5100_5200` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_5200_5300` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_5300_5400` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_5400_5500` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_5500_5600` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_5600_5700` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_5700_5800` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_5800_5900` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_5900_6000` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_6000_6100` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_600_700` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_6100_6200` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_6200_6300` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_6300_6400` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_6400_6500` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_6500_6600` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_6600_6700` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_6700_6800` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_6800_6900` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_6900_7000` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_7000_7100` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_700_800` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_7100_7200` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_7200_7300` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_7300_7400` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_7400_7500` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_7500_7600` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_7600_7700` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_7700_7800` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_7800_7900` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_7900_8000` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_8000_8100` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_800_900` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_8100_8200` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_8200_8300` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_8300_8340` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_8340_8380` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_8380_8420` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_8420_8460` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_8460_8500` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_8500_8540` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_8540_8580` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_8580_8620` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_8620_8660` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_8660_8700` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_8700_8740` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_8740_8780` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_8780_8820` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_8820_8860` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_8860_8900` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_8900_8940` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_8940_8980` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_8980_9020` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_900_1000` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9020_9060` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9060_9100` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9100_9140` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9140_9180` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9180_9220` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9220_9260` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9260_9300` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9300_9340` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9340_9380` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9380_9420` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9420_9460` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9460_9500` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9500_9540` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9540_9580` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9580_9620` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9620_9660` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9660_9700` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9700_9740` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9740_9780` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9780_9820` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9820_9860` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9860_9900` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9900_9940` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9940_9980` | propext, Classical.choice, Quot.sound |
| `FinitistProved.bbpGuardAgrees_range_9980_10001` | propext, Classical.choice, Quot.sound |
