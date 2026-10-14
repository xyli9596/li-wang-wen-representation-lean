import LiWangWenExamples38_39
import LiWangWenTheorem32
import LiWangWenCorollary33Matrix
import LiWangWenFrequencyDirect
import LiWangWenLemma51
import LiWangWenLemma51Direct
import LiWangWenTheorem31
import LiWangWenLemma52
import LiWangWenLemma52Prime
import Lean

open Lean Elab Command

def proofClosure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    if let some info := env.find? name then
      for dep in info.getUsedConstantsAsSet.toList do
        if !seen.contains dep then todo := todo.push dep
  return seen

run_cmd do
  let env ← getEnv
  let roots : Array Name := #[
    `LiWangWen.lemma_5_1_direct, `LiWangWen.lemma_5_1,
    `LiWangWen.theorem_3_2_polynomial_factors,
    `LiWangWen.theorem_3_2_polynomial_factors_recurrence,
    `LiWangWen.corollary_3_3_matrix, `LiWangWen.corollary_3_3_matrix_recurrence,
    `LiWangWen.frequency_finiteOrder_iff_isExponentialSum_direct,
    `LiWangWen.frequency_finiteOrder_iff_isExponentialSum,
    `LiWangWen.theorem_3_1, `LiWangWen.corollary_3_4,
    `LiWangWen.lemma_5_2_mean_type,
    `LiWangWen.lemma_5_2_prime_symmetric,
    `LiWangWen.example38_finiteOrder_iff,
    `LiWangWen.example39_nonzero_solution_not_finiteOrder]
  for root in roots do
    if (env.find? root).isNone then throwError "Missing endpoint: {root}"
  let rows := roots.map fun root =>
    let deps := proofClosure env root
    let localDeps := deps.toList.filter fun n =>
      ["LiWangWen.", "WimanValiron.", "Helmrath", "IncePeriodic."].any
        (fun pre => pre.isPrefixOf n.toString)
    Json.mkObj [("declaration", toJson root.toString),
      ("dependency_count", toJson deps.size),
      ("local_dependencies", toJson (localDeps.map Name.toString).mergeSort)]
  logInfo m!"ROUTE_AUDIT_JSON:{(Json.arr rows).compress}"
