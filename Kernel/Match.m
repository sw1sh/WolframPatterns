Package["Wolfram`Patterns`"]

PackageImport["Wolfram`Lazy`"]

PackageExport["MatchObjectQ"]
PackageExport["Match"]
PackageExport["MatchSum"]
PackageExport["MatchProduct"]
PackageExport["MatchPart"]
PackageExport["MatchValues"]


PackageExport["MatchParts"]
PackageExport["MatchApply"]
PackageExport["MatchBindings"]
PackageExport["MatchDefault"]
PackageExport["MatchExpand"]



SetAttributes[MatchValues, {HoldAll, SequenceHold, Flat}]
SetAttributes[MatchSum, {HoldAll, Flat}]
SetAttributes[MatchProduct, {HoldAll, Flat}]
Match

MatchObjectQ[expr_] := MatchQ[Unevaluated[expr], _MatchSum | _MatchProduct | _MatchPart | _MatchValues | _Match]

PatternHead = Pattern |
	Blank | BlankSequence | BlankNullSequence |
	HoldPattern | Verbatim |
	Alternatives | Except |
	PatternSequence | OrderlessPatternSequence | Repeated |
	Longest | Shortest |
	PatternTest | Condition |
	Optional | OptionsPattern | KeyValuePattern | IgnoringInactive;

(* MatchParts *)

MatchParts[matches_MatchValues] := ToLazyList[LazyMap[Function[v, <|{} :> v|>, HoldAllComplete], matches]]

MatchParts[MatchPart[part_, Verbatim[HoldPattern][patt_], match_]] :=
	LazyMap[
		KeyMap[If[MatchQ[Unevaluated[patt], PatternHead[___]], part, Join[part, #]] &, ReleaseLazyValue[#]] &,
		MatchParts[match]
	]

MatchParts[matches_MatchProduct] :=
	LazyFold[{parts, match} |-> With[{newParts = MatchParts[match]}, LazyCatenate @ LazyMap[part |-> LazyMap[Join[part, #] &, newParts], parts]],
		LazyList[<||>, LazyList[]],
		matches
	]

MatchParts[matches_MatchSum] := LazyCatenate @ LazyMap[MatchParts, ToLazyList[matches]]

MatchParts[LazyValue[v_] | v_] := MatchParts[v]

MatchParts[Match[m_]] := MatchParts[m]


(* MatchApply *)

(* iteratively applying match to patt in MatchProduct case can produce Sequence *)
SetAttributes[MatchApply, SequenceHold]

MatchApply[patt_, MatchValues[]] := LazyList[]
MatchApply[patt_, Verbatim[MatchValues][x_, xs___]] := LazyList[HoldComplete[x], MatchApply[Unevaluated[patt], MatchValues[xs]]]

MatchApply[Verbatim[Pattern][_, patt_] | patt_, MatchPart[part_, Verbatim[HoldPattern][subPatt_], match_]] :=
	LazyMap[
		(* EchoLabel[{part, HoldComplete[patt], #}] @ *)
		If[MatchQ[Unevaluated[patt], _PatternSequence], FlattenAt[1], Identity] @
			ReplacePart[HoldComplete[patt], With[{val = Unevaluated @@ #}, Prepend[part, 1] :> val]] &,
		(* If[MatchQ[Head[Unevaluated[subPatt]], PatternSequence | OrderlessPatternSequence], LazyMap[FlattenAt[1]], Identity] @ *)
			MatchApply[Unevaluated[subPatt], match]
	]

MatchApply[patt_, matches_MatchProduct] :=
	LazyFold[{patts, match} |-> LazyFold[LazyJoin[#1, With[{p = Unevaluated @@ #2}, MatchApply[p, match]]] &, LazyList[], patts],
		LazyList[HoldComplete[patt], LazyList[]],
		matches
	]

MatchApply[patt_, matches_MatchSum] := LazyFold[LazyJoin[#1, MatchApply[Unevaluated[patt], #2]] &, LazyList[], matches]

MatchApply[patt_, LazyValue[v_] | v_] := MatchApply[Unevaluated[patt], v]

MatchApply[patt_, Match[m_]] := MatchApply[patt, m]

MatchApply[MatchPart[_, Verbatim[HoldPattern][subPatt_], match_]] := MatchApply[Unevaluated[subPatt], match]

MatchApply[Match[m_]] := MatchApply[m]


(* MatchBindings *)

MatchBindings[MatchPart[_, Verbatim[HoldPattern][Verbatim[Pattern][name_, patt_]], match_]] :=
	LazyMap[MapValues[UnevaluatedFirst]] @ LazySelect[
		LazyMap[
			MergeIdentity,
			LazyMapThread[
				With[{val = Unevaluated @@ #2}, {{HoldPattern[name] :> val}, #1}] &,
				{
					MatchBindings[match],
					MatchApply[Unevaluated[patt], match]
				}
			]
		],
		Values[#, HoldComplete] & /* AllTrue[Function[Null, SameQ @@ HoldComplete /@ FlattenAt[#, 1], HoldAllComplete]]
	]

MatchBindings[matches_MatchProduct] :=
	LazyFold[LazyMap[MapValues[UnevaluatedFirst]] @ LazySelect[
		LazyMap[MergeIdentity, LazyTuples[{#1, MatchBindings[#2]}]],
		Values[#, HoldComplete] & /* AllTrue[Function[Null, SameQ @@ HoldComplete /@ FlattenAt[#, 1], HoldAllComplete]]
	] &, LazyList[{}, LazyList[]], matches]

MatchBindings[MatchPart[_, _, match_], opts___] := MatchBindings[match, opts]

MatchBindings[MatchPart[_, Verbatim[HoldPattern][opt_OptionValue], match_], ___] :=
	LazyMap[With[{val = Unevaluated @@ #}, {opt :> val}] &, MatchApply[Unevaluated[opt], match]]

MatchBindings[matches_MatchSum, opts___] := LazyCatenate @ LazyMap[MatchBindings[#, opts] &, ToLazyList[matches]]

MatchBindings[MatchValues[], ___] := LazyList[{}, LazyList[]]
MatchBindings[values_MatchValues, ___] := LazyConstantArray[{}, Length[HoldComplete @@ values]]

MatchBindings[LazyValue[v_], opts___] := MatchBindings[v, opts]

MatchBindings[___] := LazyList[]


(* All MatchBindings *)

FlattenBindings[expr_] := DeleteDuplicates @ Flatten[FlattenAt[HoldComplete[expr], 1], 1, HoldComplete]

MatchBindings[MatchPart[_, Verbatim[HoldPattern][Verbatim[Pattern][name_, patt_]], match_], All] :=
	LazyMap[MapValues[FlattenBindings]] @ LazyMap[
		MergeIdentity,
		LazyCatenate @ LazyMap[
			LazyMapThread[
				With[{val = HoldComplete @@ #2}, {{HoldPattern[name] :> #2}, #1}] &,
				{MatchBindings[#, All], MatchApply[Unevaluated[patt], #]}
			] &,
			ToLazyList[MatchExpand[match]]
		]
	]

MatchBindings[matches_MatchProduct, All] :=
	LazyFold[LazyMap[MapValues[FlattenBindings]] @ LazyMap[MergeIdentity, LazyTuples[{#1, MatchBindings[#2, All]}]] &, LazyList[{}, LazyList[]], matches]


MatchBindings[Match[match_], opts___] := MatchBindings[match, opts]


(* MatchExpand *)

MatchExpand[matches_MatchSum] := LazyMap[MatchExpand, matches]

(* MatchExpand[MatchProduct[]] := MatchSum[MatchProduct[]] *)

MatchExpand[matches_MatchProduct] :=
	With[{expand = List @@ LazyListToList[matches]},
		If[	Length[expand] > 0,
			MatchSum @@ LazyListToList @ LazyMap[ToLazyList[#, MatchProduct] &, LazyTuples[Map[List @@ LazyListToList[MatchExpand[#]] &, expand]]],
			MatchSum[MatchProduct[]]
		]
	]
	(* LazySelect[
		LazyMap[ToLazyList[#, MatchProduct] &, LazyTuples[Map[ToLazyList @ LazyListToList[MatchExpand[#]] &, List @@ LazyListToList[matches]]]],
		ReleaseLazyValue[LazyFirst[MatchBindings[#], None]] =!= None &
	], *)


MatchExpand[MatchPart[part_, patt_, match_]] := ToLazyList[LazyMap[MatchPart[part, patt, #] &, ToLazyList[MatchExpand[match]]], MatchSum]

MatchExpand[MatchValues[]] := MatchSum[MatchProduct[]]

MatchExpand[values_MatchValues] := MatchSum @@ MatchValues /@ HoldComplete @@ values

MatchExpand[Match[m_]] := Match[MatchExpand[m]]


MatchDefault[patt_, includePatternsQ_ : True] := Block[{optPos = Position[Unevaluated[patt], Verbatim[Optional][_Pattern, ___]], pattPos},
	pattPos = If[TrueQ[includePatternsQ],
		Select[Position[Unevaluated[patt], _Pattern], p |-> NoneTrue[optPos, MatchQ[p, Append[#, ___]] &]],
		{}
	];
	MatchProduct @@ KeyValueMap[
		Which[
			MatchQ[#2, Verbatim[HoldPattern][Verbatim[Optional][_, _]]],
			With[{def = #2[[1, 2]]},
				MatchPart[#1, ReplaceAt[#2, Verbatim[Optional][p_, ___] :> p, {1}], MatchValues[def, Sequence[]]]
			],
			Length[#1] > 0,
			With[{i = Last[#1], head = Unevaluated @@ Extract[Unevaluated[patt], Append[Most[#1], 0], Hold]},
				With[{def = Default[head, i]},
					MatchPart[#1, ReplaceAt[#2, Verbatim[Optional][p_, ___] :> p, {1}],
						If[def === Unevaluated[Default[head, i]], MatchValues[Sequence[]], MatchValues[def, Sequence[]]]
					]
				]
			],
			True,
			MatchPart[#1, ReplaceAt[#2, Verbatim[Optional][p_, ___] :> p, {1}], MatchValues[Sequence[]]]
		] &,
		Join[
			AssociationThread[optPos, Extract[Unevaluated[patt], optPos, HoldPattern]],
			AssociationThread[pattPos, Extract[Unevaluated[patt], pattPos, HoldPattern]]
		]
	]
]


MakeBoxes[m_Match, form_] ^:= With[{
    icon = Framed["\[Ellipsis]"]
},
    BoxForm`ArrangeSummaryBox[
        "Match",
        m,
        icon,
        {{}},
        {{BoxForm`SummaryItem[{m[[1, 0]]}]}},
        form,
		"Interpretable" -> Automatic
	]
]

