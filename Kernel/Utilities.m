Package["Wolfram`Patterns`"]

PackageScope["HoldApply"]
PackageScope["MergeIdentity"]
PackageScope["MapValues"]
PackageScope["UnevaluatedExtract"]
PackageScope["UnevaluatedFirst"]
PackageScope["UnevaluatedFlatten"]
PackageScope["mosts"]
PackageScope["rests"]
PackageScope["splits"]
PackageScope["LengthAt"]
PackageScope["FoldTakeWhile"]



HoldApply[f_, x_, g_ : Unevaluated] := g @@ f @@@ HoldComplete[x]

MergeIdentity[rules : {({(_Rule | _RuleDelayed)...} | _Association) ...}] := With[{merge = Merge[rules, HoldComplete]},
	MapThread[With[{v = Unevaluated @@ #2}, #1 :> v] &, {Keys[merge], FlattenAt[1] /@ Values[merge, HoldComplete]}]
]

MapValues[f_, a : {(_Rule | _RuleDelayed)...} | _Association] :=
	MapThread[With[{v = Unevaluated @@ #2},
		With[{w = Unevaluated @@ HoldComplete[Evaluate @ f[v]]}, #1 :> w]] &, {Keys[a], Values[a, HoldComplete]}
	]
MapValues[f_][a_] := MapValues[f, a]

UnevaluatedExtract[expr_, pos_] := Unevaluated @@ Extract[Unevaluated @ expr, pos, HoldComplete]
UnevaluatedFirst[expr_] := UnevaluatedExtract[Unevaluated @ expr, 1]

mosts[expr_] := NestList[Most, expr, Length[expr]]
rests[expr_] := NestList[Rest, expr, Length[expr]]


splits[expr_, 1] := {{expr}}
splits[expr_, n_Integer ? Positive] :=
	Catenate[(subExpr |-> Join[TakeDrop[First[subExpr], #], Rest[subExpr]]  & /@ Range[0, Length[First[subExpr]]]) /@ splits[expr, n - 1]]
splits[expr_] := splits[expr, 2]

LengthAt[expr_, pos_] := Extract[expr, pos, Function[Null, Length[Unevaluated[#]], HoldAllComplete]]

FoldTakeWhile[f_, l_, n_, g_ : List] :=
	Take[FoldWhile[Function[Null, g[#1, f[#2]], HoldAllComplete], g[], l, Length[#] < n &], UpTo[n]]

