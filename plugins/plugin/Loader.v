Declare ML Module "rocq-certirocq.plugin".

CertiRocq Extract Inductives [ bool => "bool" [ 1 0 ] ].

Ltac eval_certirocq c := certirocq_eval -unsafe-erasure (let x := c in x) (fun v => exact v).
Notation "'CertiEval' c" := ltac:(eval_certirocq c) (at level 0, c at level 200, only parsing).

Ltac eval_certirocq_typed c := certirocq_eval -unsafe-erasure -typed-erasure (let x := c in x) (fun v => exact v).
Notation "'CertiEvalTyped' c" := ltac:(eval_certirocq_typed c) (at level 0, c at level 200, only parsing).
