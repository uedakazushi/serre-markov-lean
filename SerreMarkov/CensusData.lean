import SerreMarkov.CensusPart010

/-! All 10,395 witnesses assembled from independently kernel-checked chunks.
The preceding module chain enforces bounded-memory sequential builds. -/

set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 100000000

namespace SerreMarkov.IndexTwelve

def allCensusChunks : List (List CensusRow) := [
  censusChunk000,
  censusChunk001,
  censusChunk002,
  censusChunk003,
  censusChunk004,
  censusChunk005,
  censusChunk006,
  censusChunk007,
  censusChunk008,
  censusChunk009,
  censusChunk010,
  censusChunk011,
  censusChunk012,
  censusChunk013,
  censusChunk014,
  censusChunk015,
  censusChunk016,
  censusChunk017,
  censusChunk018,
  censusChunk019,
  censusChunk020,
  censusChunk021,
  censusChunk022,
  censusChunk023,
  censusChunk024,
  censusChunk025,
  censusChunk026,
  censusChunk027,
  censusChunk028,
  censusChunk029,
  censusChunk030,
  censusChunk031,
  censusChunk032,
  censusChunk033,
  censusChunk034,
  censusChunk035,
  censusChunk036,
  censusChunk037,
  censusChunk038,
  censusChunk039,
  censusChunk040,
  censusChunk041,
  censusChunk042,
  censusChunk043,
  censusChunk044,
  censusChunk045,
  censusChunk046,
  censusChunk047,
  censusChunk048,
  censusChunk049,
  censusChunk050,
  censusChunk051,
  censusChunk052,
  censusChunk053,
  censusChunk054,
  censusChunk055,
  censusChunk056,
  censusChunk057,
  censusChunk058,
  censusChunk059,
  censusChunk060,
  censusChunk061,
  censusChunk062,
  censusChunk063,
  censusChunk064,
  censusChunk065,
  censusChunk066,
  censusChunk067,
  censusChunk068,
  censusChunk069,
  censusChunk070,
  censusChunk071,
  censusChunk072,
  censusChunk073,
  censusChunk074,
  censusChunk075,
  censusChunk076,
  censusChunk077,
  censusChunk078,
  censusChunk079,
  censusChunk080,
  censusChunk081,
  censusChunk082,
  censusChunk083,
  censusChunk084,
  censusChunk085,
  censusChunk086,
  censusChunk087,
  censusChunk088,
  censusChunk089,
  censusChunk090,
  censusChunk091,
  censusChunk092,
  censusChunk093,
  censusChunk094,
  censusChunk095,
  censusChunk096,
  censusChunk097,
  censusChunk098,
  censusChunk099,
  censusChunk100,
  censusChunk101,
  censusChunk102,
  censusChunk103
]

def allCensusRows : List CensusRow := allCensusChunks.flatten

theorem allCensusChunks_checked :
    ∀ chunk ∈ allCensusChunks, ∀ row ∈ chunk, row.Valid := by
  simp only [allCensusChunks, List.forall_mem_cons]
  exact ⟨censusChunk000_checked, ⟨censusChunk001_checked, ⟨censusChunk002_checked, ⟨censusChunk003_checked, ⟨censusChunk004_checked, ⟨censusChunk005_checked, ⟨censusChunk006_checked, ⟨censusChunk007_checked, ⟨censusChunk008_checked, ⟨censusChunk009_checked, ⟨censusChunk010_checked, ⟨censusChunk011_checked, ⟨censusChunk012_checked, ⟨censusChunk013_checked, ⟨censusChunk014_checked, ⟨censusChunk015_checked, ⟨censusChunk016_checked, ⟨censusChunk017_checked, ⟨censusChunk018_checked, ⟨censusChunk019_checked, ⟨censusChunk020_checked, ⟨censusChunk021_checked, ⟨censusChunk022_checked, ⟨censusChunk023_checked, ⟨censusChunk024_checked, ⟨censusChunk025_checked, ⟨censusChunk026_checked, ⟨censusChunk027_checked, ⟨censusChunk028_checked, ⟨censusChunk029_checked, ⟨censusChunk030_checked, ⟨censusChunk031_checked, ⟨censusChunk032_checked, ⟨censusChunk033_checked, ⟨censusChunk034_checked, ⟨censusChunk035_checked, ⟨censusChunk036_checked, ⟨censusChunk037_checked, ⟨censusChunk038_checked, ⟨censusChunk039_checked, ⟨censusChunk040_checked, ⟨censusChunk041_checked, ⟨censusChunk042_checked, ⟨censusChunk043_checked, ⟨censusChunk044_checked, ⟨censusChunk045_checked, ⟨censusChunk046_checked, ⟨censusChunk047_checked, ⟨censusChunk048_checked, ⟨censusChunk049_checked, ⟨censusChunk050_checked, ⟨censusChunk051_checked, ⟨censusChunk052_checked, ⟨censusChunk053_checked, ⟨censusChunk054_checked, ⟨censusChunk055_checked, ⟨censusChunk056_checked, ⟨censusChunk057_checked, ⟨censusChunk058_checked, ⟨censusChunk059_checked, ⟨censusChunk060_checked, ⟨censusChunk061_checked, ⟨censusChunk062_checked, ⟨censusChunk063_checked, ⟨censusChunk064_checked, ⟨censusChunk065_checked, ⟨censusChunk066_checked, ⟨censusChunk067_checked, ⟨censusChunk068_checked, ⟨censusChunk069_checked, ⟨censusChunk070_checked, ⟨censusChunk071_checked, ⟨censusChunk072_checked, ⟨censusChunk073_checked, ⟨censusChunk074_checked, ⟨censusChunk075_checked, ⟨censusChunk076_checked, ⟨censusChunk077_checked, ⟨censusChunk078_checked, ⟨censusChunk079_checked, ⟨censusChunk080_checked, ⟨censusChunk081_checked, ⟨censusChunk082_checked, ⟨censusChunk083_checked, ⟨censusChunk084_checked, ⟨censusChunk085_checked, ⟨censusChunk086_checked, ⟨censusChunk087_checked, ⟨censusChunk088_checked, ⟨censusChunk089_checked, ⟨censusChunk090_checked, ⟨censusChunk091_checked, ⟨censusChunk092_checked, ⟨censusChunk093_checked, ⟨censusChunk094_checked, ⟨censusChunk095_checked, ⟨censusChunk096_checked, ⟨censusChunk097_checked, ⟨censusChunk098_checked, ⟨censusChunk099_checked, ⟨censusChunk100_checked, ⟨censusChunk101_checked, ⟨censusChunk102_checked, ⟨censusChunk103_checked, (by intro x hx; cases hx)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem allCensusRows_checked : ∀ row ∈ allCensusRows, row.Valid := by
  intro row hrow
  obtain ⟨chunk, hchunk, hmem⟩ := List.mem_flatten.mp hrow
  exact allCensusChunks_checked chunk hchunk row hmem

end SerreMarkov.IndexTwelve
