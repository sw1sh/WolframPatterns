Package["Wolfram`Patterns`"]

PackageImport["Wolfram`Lazy`"]


PackageExport["MatchSum"]
PackageExport["MatchProduct"]
PackageExport["MatchPart"]
PackageExport["MatchValues"]


PackageExport["MatchApply"]
PackageExport["MatchBindings"]
PackageExport["MatchDefault"]
(* PackageExport["LazySubstitutionExpand"] *)



SetAttributes[MatchValues, {HoldAllComplete, Flat}]
SetAttributes[MatchSum, {HoldAll, Flat}]
SetAttributes[MatchProduct, {HoldAll, Flat}]

MatchPart[{}, _, subst : (MatchSum | MatchProduct | MatchValues)[]] := subst

MatchProduct[___, MatchSum[], ___] := MatchSum[]

MatchProduct[left___, MatchValues[], right___] := MatchProduct[left, right]


(* MatchApply *)

MatchApply[patt_, MatchValues[]] := LazyList[]
MatchApply[patt_, Verbatim[MatchValues][x_, xs___]] := LazyList[HoldComplete[x], MatchApply[patt, MatchValues[xs]]]

MatchApply[patt_, MatchPart[part_, Verbatim[HoldPattern][subPatt_], subst_]] :=
	LazyMap[
		If[MatchQ[#, HoldComplete[_Sequence]], FlattenAt[Prepend[part, 1]], Identity] @
			ReplacePart[HoldComplete[patt], With[{val = Unevaluated @@ #}, Prepend[part, 1] :> val]] &,
		If[MatchQ[Head[Unevaluated[subPatt]], PatternSequence | OrderlessPatternSequence], LazyMap[FlattenAt[1]], Identity] @
			MatchApply[Unevaluated[subPatt], subst]
	]

MatchApply[patt_, substs_MatchProduct] :=
	LazyFold[{patts, subst} |-> LazyFold[LazyJoin[#1, With[{p = Unevaluated @@ #2}, MatchApply[p, subst]]] &, LazyList[], patts],
		{HoldComplete[patt]},
		substs
	]

MatchApply[patt_, substs_MatchSum] := LazyFold[LazyJoin[#1, MatchApply[patt, #2]] &, LazyList[], substs]


(* MatchBindings *)

MatchBindings[MatchPart[_, Verbatim[HoldPattern][Verbatim[Pattern][name_, patt_]], subst_]] := With[{
	bindings = LazyMap[With[{val = Unevaluated @@ #}, <|name :> val|>] &, ReleaseLazy @ MatchApply[Unevaluated[patt], subst]]
},
	LazyMap[MapValues[UnevaluatedFirst]] @ LazySelect[
		LazyMap[MergeIdentity, LazyTuples[{bindings, ReleaseLazy @ MatchBindings[subst]}]],
		AllTrue[Function[Null, SameQ @@ HoldComplete /@ FlattenAt[HoldComplete[#], 1], HoldAllComplete]]
	]
]

MatchBindings[MatchPart[_, Verbatim[HoldPattern][opt_OptionsPattern], subst_]] :=
	With[{val = Unevaluated @@ #}, <|OptionsPattern[] :> val|>] & /@ MatchApply[Unevaluated[opt], subst, n]

MatchBindings[MatchPart[_, _, subst_]] := MatchBindings[subst]

MatchBindings[substs_MatchSum] := LazyFold[LazyJoin[#1, ReleaseLazy @ MatchBindings[#2]] &, LazyList[], substs]

MatchBindings[substs_MatchProduct] :=
	LazyFold[LazyMap[MapValues[UnevaluatedFirst]] @ LazySelect[
		LazyMap[MergeIdentity, LazyTuples[{#1, ReleaseLazy @ MatchBindings[#2]}]],
		AllTrue[Function[Null, SameQ @@ HoldComplete /@ FlattenAt[HoldComplete[#], 1], HoldAllComplete]]
	] &, LazyList[<||>, LazyList[]], substs]

MatchBindings[MatchValues[]] := LazyList[<||>, LazyList[]]
MatchBindings[values_MatchValues] := LazyFold[LazyList[<||>, #1] &, LazyList[], values]

MatchBindings[Lazy[subst_]] := MatchBindings[subst]



MatchDefault[patt_] := DefaultSubstitutions[patt] /. {
	PartSubstitution -> MatchPart,
	SubstitutionProduct -> MatchProduct,
	SubstitutionSum -> MatchSum,
	SubstitutionValues -> MatchValues
}


MatchBoxes[m_, form_] := With[{
    icon = Framed["\[Ellipsis]"]
},
    BoxForm`ArrangeSummaryBox[
        "Match",
        m,
        icon,
        {{}},
        {{}},
        form,
		"Interpretable" -> Automatic
	]
]

MakeBoxes[m_MatchPart, form_] ^:= MatchBoxes[m, form]
MakeBoxes[m_MatchProduct, form_] ^:= MatchBoxes[m, form]
MakeBoxes[m_MatchSum, form_] ^:= MatchBoxes[m, form]
MakeBoxes[m_MatchValues, form_] ^:= MatchBoxes[m, form]

