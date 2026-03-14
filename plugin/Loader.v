Declare ML Module "rocq-certirocq.plugin".

CertiRocq Extract Inductives [ bool => "bool" [ 1 0 ] ].

Ltac eval_certirocq c := certirocq_eval (let x := c in x) (fun v => exact v).
Notation "'CertiEval' c" := ltac:(eval_certirocq c) (at level 0, c at level 200, only parsing).
