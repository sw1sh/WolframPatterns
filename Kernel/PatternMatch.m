Package["Wolfram`Patterns`"]

PackageImport["Wolfram`Lazy`"]

PackageExport["PatternMatch"]
PackageExport["AlternativesSequence"]
PackageExport["DefaultAlternatives"]
PackageExport["DefaultAlternativesSequence"]
PackageExport["NameValuePattern"]
PackageExport["DeepPattern"]
PackageExport["DefaultOptionsPattern"]
PackageExport["NestedNull"]
PackageExport["Nested"]



SequenceSplits[args_, emptyRight_ : False, defaultMode_ : Automatic] := With[{mode = Replace[defaultMode, Except[Longest | Shortest] -> Shortest]},
    If[ TrueQ[emptyRight],
        MatchSum[{args, HoldComplete[]}],
        LazyMap[LazyListToList] @ Switch[mode,
            Shortest,
            LazySplits[args, MatchSum],
            Longest,
            LazySplitsReverse[args, MatchSum]
        ]
    ]
]

ShortestTriples[xs_] := ToLazyList[
    LazyMap[LazyListToList] @ LazyCatenate @ LazyMap[n |-> LazyCatenate @ LazyMap[split |-> With[{first = LazyFirst[split]},
	    If[Length[xs] - Length[first] < n, LazyList[], LazyMap[LazyList[first, ToLazyList[TakeDrop[#, UpTo[n]]]] &, LazyRest[split]]]], LazySplits[xs]], LazyRange[0, Length[xs]]],
    MatchSum
]

LongestTriples[xs_] := ToLazyList[
    LazyMap[LazyListToList] @ LazyCatenate @ LazyMap[n |-> LazyCatenate @ LazyMap[split |-> With[{first = LazyFirst[split]},
	    If[Length[xs] - Length[first] < n, LazyList[], LazyMap[LazyList[first, ToLazyList[TakeDrop[#, UpTo[n]]]] &, LazyRest[split]]]], LazySplitsReverse[xs]], LazyRange[Length[xs], 0, -1]],
    MatchSum
]


MapMatchPart[f_, matches : _MatchSum | _MatchProduct] := LazyMap[MapMatchPart[f, #] &, matches]
MapMatchPart[f_, match : MatchPart[{}, p_, m_]] := f[MatchPart[{}, p, MapMatchPart[f, m]]]
MapMatchPart[f_, match_MatchPart] := f[match]
MapMatchPart[_, match_MatchValues] := match
(* MapMatchPart[f_, LazyValue[v_] | v_] := MapMatchPart[f, v] *)

MapMatchValues[f_, matches : _MatchSum | _MatchProduct] := LazyMap[MapMatchValues[f, #] &, matches]
MapMatchValues[f_, MatchPart[part_, patt_, match_]] := MatchPart[part, f[patt], MapMatchValues[f, match]]
MapMatchValues[f_, match_MatchValues] := f[match]
(* MapMatchValues[f_, LazyValue[v_] | v_] := MapMatchValues[f, v] *)


FlattenIdentities[expr_] := FlattenAt[expr, Position[expr, _[_], {1}, Heads -> False]]


patternMatchShift[seq_HoldComplete, head_Symbol[patt___], shift : _Integer ? NonNegative : 0, drop : True | False : False] := With[{
    val = Unevaluated @@ head @@@ HoldComplete[seq]
},
    MapMatchPart[
        Replace[{
            MatchPart[{0, ___}, ___] :> MatchProduct[],
            MatchPart[{}, _, m_] :> m,
            If[ drop,
                MatchPart[{_, ps___}, rest___] :> MatchPart[{ps}, rest],
                If[shift > 0, MatchPart[{p_, ps___}, rest___] :> MatchPart[{p + shift, ps}, rest], Nothing]
            ]
        }],
        patternMatch[val, Unevaluated[head[patt]]]
    ]
]


(* PatternMatch *)

SetAttributes[patternMatch, SequenceHold]
SetAttributes[PatternMatch, SequenceHold]


patternMatch[Sequence[args___], Sequence[patt___]] :=
    MatchPart[{}, HoldPattern[PatternSequence[patt]], patternMatch[HoldComplete[args], HoldComplete[patt]]]


(* OneIdentity *)

patternMatch[expr : Except[head_Symbol[___]], head_Symbol[patt___]] /; MemberQ[Attributes[head], OneIdentity] :=
    patternMatch[Unevaluated[head[expr]], Unevaluated[head[patt]]]


(* Orderless *)

patternMatch[head_Symbol[args___], head_Symbol[patt___]] /;
    Not[Length[Unevaluated[{patt}]] == 1 && Head[Unevaluated[patt]] === OrderlessPatternSequence] && MemberQ[Attributes[head], Orderless] :=
    Module[{h},
        DefaultValues[h] = DefaultValues[head] /. head :> h;
        SetAttributes[h, DeleteCases[Attributes[head], Orderless]];
        MapMatchValues[
            ReplaceAll[h :> head],
            patternMatch[Unevaluated[h[args]], Unevaluated[h[OrderlessPatternSequence[patt]]]]
        ]
    ]


(* OrderlessPatternSequence *)

patternMatch[Sequence[args___], Verbatim[OrderlessPatternSequence][patt___]] :=
    patternMatch[Unevaluated[HoldComplete[args]], Unevaluated[HoldComplete[OrderlessPatternSequence[patt]]]]

patternMatch[arg_, Verbatim[OrderlessPatternSequence][patt___]] :=
    patternMatch[Unevaluated[HoldComplete[arg]], Unevaluated[HoldComplete[OrderlessPatternSequence[patt]]]]

patternMatch[head_Symbol[args___], head_Symbol[left : Verbatim[OrderlessPatternSequence][patt___], right___]] :=
    MatchPart[{}, HoldPattern[head[patt, right]],
        LazyMap[Apply[{l, r} |->
            LazyMap[
                patternMatchShift[Join[#, r], Unevaluated[head[patt, right]]] &,
                ToLazyList[LazyPermutations[l], MatchSum]
            ]
        ],
        SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0]
    ]
    ]


(* Flat *)
(* should be after OrderlessPatternSequence *)

patternMatch[head_Symbol[args___], head_Symbol[patt__]] /; MemberQ[Attributes[head], Flat] := Module[{h},
    DefaultValues[h] = DefaultValues[head] /. head :> h;
    SetAttributes[h, DeleteCases[Attributes[head], Flat]];
    MatchPart[{}, HoldPattern[head[patt]], MapMatchValues[
        ReplaceAll[h :> head],
        LazyMap[
            With[{v = If[MemberQ[Attributes[head], OneIdentity], FlattenIdentities, Identity][h @@@ HoldComplete @@ Flatten /@ HoldComplete @@@ Normal[#]]},
                (* EchoFunction[ResourceFunction["PrettyForm"][{v, h[patt]}], MatchBindings /* Normal]@ *)
                patternMatchShift[v, Unevaluated[h[patt]]]
            ] &,
            LazySplits[HoldComplete /@ Unevaluated[{args}], Length[HoldComplete[patt]], MatchSum]
        ]
    ]]
]


(* PatternSequence *)

patternMatch[Sequence[args___], Verbatim[PatternSequence][patt___]] :=
    patternMatch[Unevaluated[Sequence[args]], Unevaluated[Sequence[patt]]]

patternMatch[arg_, Verbatim[PatternSequence][patt___]] :=
    patternMatch[Unevaluated[Sequence[arg]], Unevaluated[Sequence[patt]]]

patternMatch[head_Symbol[args___], head_Symbol[left : Verbatim[PatternSequence][patt___], right___]] :=
    MatchPart[{}, HoldPattern[head[patt, right]],
        LazyMap[Apply[{l, r} |->
            patternMatchShift[Join[l, r], Unevaluated[head[patt, right]]]
        ],
        SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0]
    ]
    ]


(* Shortest *)

patternMatch[Sequence[args___], Verbatim[Shortest][patt_]] :=
    patternMatch[Unevaluated[Sequence[args]], Unevaluated[Sequence[Shortest[patt]]]]

patternMatch[head_Symbol[args___], head_Symbol[left___, mid : Verbatim[Shortest][patt_], right___]] := With[{
    l = Length[Hold[left]], r = Length[Hold[right]]
},
    MatchPart[
        {},
        HoldPattern[head[left, mid, right]],
        LazyMap[Apply[
            If[ l == 0 && Length[#1] > 0 || r == 0 && Length[#3] > 0,
                MatchSum[],
                MatchProduct[
                    If[ l == 0,
                        MatchProduct[],
                        patternMatchShift[#1, Unevaluated[head[left]]]
                    ],
                    MatchPart[{l + 1},
                        HoldPattern[mid],
                        patternMatchShift[#2, Unevaluated[head[patt]], l]
                    ],
                    If[ r == 0,
                        MatchProduct[],
                        patternMatchShift[#3, Unevaluated[head[right]], l + 1]
                    ]
                ]
            ] &
        ],
            ShortestTriples[HoldComplete[args]]
        ]
    ]
]


(* Longest *)

patternMatch[Sequence[args___], Verbatim[Longest][patt_]] :=
    patternMatch[Unevaluated[Sequence[args]], Unevaluated[Sequence[Longest[patt]]]]

patternMatch[head_Symbol[args___], head_Symbol[left___, mid : Verbatim[Longest][patt_], right___]] := With[{
    l = Length[HoldComplete[left]], r = Length[HoldComplete[right]]
},
    MatchPart[
        {},
        HoldPattern[head[left, mid, right]],
        LazyMap[Apply[
            If[ l == 0 && Length[#1] > 0 || r == 0 && Length[#3] > 0,
                MatchSum[],
                MatchProduct[
                    If[ l == 0,
                        MatchProduct[],
                        patternMatchShift[#1, Unevaluated[head[left]]]
                    ],
                    MatchPart[{l + 1},
                        HoldPattern[mid],
                        patternMatchShift[#2, Unevaluated[head[patt]], l]
                    ],
                    If[ r == 0,
                        MatchProduct[],
                        patternMatchShift[#3, Unevaluated[head[right]], l + 1]
                    ]
                ]
            ] &
        ],
            LongestTriples[HoldComplete[args]]
        ]
    ]
]


(* Pattern *)

patternMatch[expr_, patt : Verbatim[Pattern][_Symbol, subPatt_]] :=
	MatchPart[{}, HoldPattern[patt], patternMatch[Unevaluated[expr], Unevaluated[subPatt]]]

patternMatch[head_Symbol[args___], head_Symbol[left : Verbatim[Pattern][name_Symbol, patt_], right___]] := MatchPart[
    {},
    HoldPattern[head[left, right]],
    LazyMap[Apply[
        MatchProduct[
            MatchPart[{1},
                Pattern @@@ If[MatchQ[Unevaluated[patt], _PatternSequence], FlattenAt[{1, 2}], Identity] @
                    HoldPattern[Hold[name, PatternSequence[patt]]],
                patternMatchShift[#1, Unevaluated[head[patt]]]
            ],
            patternMatchShift[#2, Unevaluated[head[right]], 1]
        ] &],
        SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0]
    ]
]


(* Blank *)

patternMatch[expr_, Verbatim[Blank][]] := MatchValues[expr]

patternMatch[expr_, Verbatim[Blank][h_]] := With[{head = Unevaluated @@ Head[Unevaluated[expr], HoldComplete]},
	MatchProduct[patternMatch[head, h], MatchValues[expr]]]

patternMatch[head_Symbol[args___], head_Symbol[left : Verbatim[Blank][h___], right___]] := MatchPart[
    {},
    HoldPattern[head[left, right]],
    LazyMap[Apply[
        MatchProduct[
            MatchPart[{1},
                HoldPattern[left],
                HoldApply[
                    If[MemberQ[Attributes[head], Flat], head, Sequence],
                    #1,
                    MatchValues
                ]
            ],
            patternMatchShift[#2, Unevaluated[head[right]], 1]
        ] &],
        If[ MemberQ[Attributes[head], Flat], Identity, LazySelect[#, MatchQ[#[[1]], HoldComplete[_h]] &] &] @
            LazyRotateLeft @ SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0]
    ]
]


(* BlankSequence *)

patternMatch[Sequence[args___], Verbatim[BlankSequence][h___]] :=
    If[ MatchQ[HoldComplete[args], HoldComplete[__h]],
	    MatchValues[Sequence[args]],
        MatchSum[]
    ]

patternMatch[arg_, Verbatim[BlankSequence][h___]] :=
    If[ MatchQ[HoldComplete[arg], HoldComplete[_h]],
	    MatchValues[arg],
        MatchSum[]
    ]

patternMatch[head_Symbol[args__], head_Symbol[left : Verbatim[BlankSequence][h___], right___]] := MatchPart[
    {},
    HoldPattern[head[left, right]],
	LazyMap[Apply[
        MatchProduct[
            MatchPart[{1}, HoldPattern[left], HoldApply[Sequence, #1, MatchValues]],
            patternMatchShift[#2, Unevaluated[head[right]], 1]
        ] &],
		LazySelect[
			SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0],
			MatchQ[#[[1]], HoldComplete[__h]] &
		]
	]
]


(* BlankNullSequence *)

patternMatch[Sequence[args___], Verbatim[BlankNullSequence][h___]] :=
    If[ MatchQ[HoldComplete[args], HoldComplete[___h]],
	    MatchValues[Sequence[args]],
        MatchSum[]
    ]

patternMatch[arg_, Verbatim[BlankNullSequence][h___]] :=
    If[ MatchQ[HoldComplete[arg], HoldComplete[_h]],
	    MatchValues[arg],
        MatchSum[]
    ]

patternMatch[head_Symbol[args___], head_Symbol[left : Verbatim[BlankNullSequence][h___], right___]] := MatchPart[
    {},
    HoldPattern[head[left, right]],
	LazyMap[Apply[
        MatchProduct[
            MatchPart[{1}, HoldPattern[left], HoldApply[Sequence, #1, MatchValues]],
            patternMatchShift[#2, Unevaluated[head[right]], 1]
        ] &],
		LazySelect[
			SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0],
			MatchQ[#[[1]], HoldComplete[___h]] &
		]
	]
]


(* RepeatedNull *)

patternMatch[head_Symbol[args___], head_Symbol[left : Verbatim[RepeatedNull][patt_, spec_ : Infinity], right___]] := With[{
    min = Replace[spec, {{k_} :> k, {min_, _} :> min, _ -> 0}],
    max = Replace[spec, {{k_} :> k, {_, max_} :> max}]
},
With[{
    numRepeats = max - min + 1
},
    MatchPart[
    {},
    HoldPattern[head[left, right]],
	LazyMap[
        Apply[{l, r} |->
            ToLazyList[
                LazyMap[First] @ ReleaseLazyValue @ LazyNestWhile[
                    LazyCatenate @ LazyMap[
                        With[{
                            prevSubst = #[[1]],
                            len = Length[#[[2]]],
                            i = #[[3]],
                            val = Unevaluated @@ head @@@ HoldComplete @@ {#[[2]]},
                            p = If[
                                #[[3]] == 0,
                                Unevaluated @@ head @@@ HoldComplete @@ {Append[Flatten[HoldComplete @@ Table[HoldComplete[patt], min]], rest___]},
                                Unevaluated @@ {head[patt, rest___]}
                            ],
                            restPos = If[#[[3]] == 0, min + 1, 2]
                        },
                            Which[
                                (* input sequence is empty*)
                                len == 0,
                                LazyList[Evaluate[{
                                    MatchProduct[
                                        MatchPart[{1},
                                            HoldPattern[left],
                                            If[
                                                i == 0 && min > 0,
                                                MatchSum[],
                                                MatchPart[{},
                                                    PatternSequence @@@ HoldPattern[Evaluate[Flatten[Hold @@ Table[Hold[patt], min + i - 1 ]]]],
                                                    prevSubst
                                                ]
                                            ]
                                        ],
                                        (* EchoFunction[{l, r, head[right], i}, Normal @* MatchBindings]@ *)
                                        patternMatchShift[r, Unevaluated[head[right]], 1]
                                    ],
                                    #[[2]], #[[3]] + 1}], LazyList[]],
                                (* last iteration but input is not empty *)
                                i == numRepeats,
                                LazyList[],
                                True,
                                Block[{subst = LazyListToList @ MatchExpand @ patternMatch[val, p]}, LazySelect[# =!= Nothing &] @ LazyMap[
                                    With[{next = HoldComplete @@ Lookup[ReleaseLazyValue @ LazyFirst[MatchBindings[#], {}], HoldPattern[rest], Null, Hold]},
                                        If[ next =!= Null && Length[next] <= len,
                                            {
                                                MatchProduct[
                                                    prevSubst,
                                                    MapMatchPart[
                                                        Replace[{
                                                            (* replace with dummy sequence *)
                                                            MatchPart[{restPos}, __] -> MatchProduct[],
                                                            MatchPart[{p_, ps___}, rest___] :> MatchPart[{If[i == 0, p, i], ps}, rest],
                                                            MatchPart[{}, _, m_] :> m
                                                        }],
                                                        #
                                                    ]
                                                ],
                                                next,
                                                i + 1
                                            },
                                            Nothing
                                        ]
                                    ] &,
                                    ToLazyList[subst]
                                ]
                                ]
                            ]
                        ] &,
                        #
                    ] &,
                    LazyList[{MatchProduct[], l, 0}, LazyList[]],
                    ReleaseLazyValue[LazyAnyTrue[#, #[[3]] == 0 || Length[#[[2]]] > 0 &]] &,
                    1,
                    numRepeats,
                    1
                ],
                MatchSum
            ]
        ],
        SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0]
    ]
]]]


(* Repeated *)

patternMatch[head_Symbol[args___], head_Symbol[Verbatim[Repeated][patt_, spec_ : Infinity], right___]] := With[{
    newSpec = Replace[spec, {k : Except[_List] :> {1, k}}]
},
    patternMatch[Unevaluated[head[args]], Unevaluated[head[RepeatedNull[patt, newSpec], right]]]
]


(* AlternativesSequence *)

patternMatch[head_Symbol[args___], head_Symbol[left : Verbatim[AlternativesSequence][patt___], right___]] := MatchPart[
    {},
    HoldPattern[head[left, right]],
    LazyMap[
        Apply[MatchProduct[
            MatchPart[{1},
                HoldPattern[left],
                With[{holdPatt = head @@@ Hold[Evaluate @ Flatten[Hold @@ Table[Hold[Alternatives[patt]], Length[#1]]]]},
                    MatchPart[{}, PatternSequence @@@ HoldPattern @@ holdPatt,
                        With[{p = Unevaluated @@ holdPatt},
                            patternMatchShift[#1, p]
                        ]
                    ]
                ]
            ],
            patternMatchShift[#2, Unevaluated[head[right]], 1]
        ] &],
        SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0]
    ]
]

patternMatch[head_Symbol[args___], head_Symbol[left : Verbatim[DefaultAlternativesSequence][patt___], right___]] := MatchPart[
    {},
    HoldPattern[head[left, right]],
    LazyMap[
        Apply[MatchProduct[
            MatchPart[{1},
                HoldPattern[left],
                With[{holdPatt = head @@@ Hold[Evaluate @ Flatten[Hold @@ Table[Hold[DefaultAlternatives[patt]], Length[#1]]]]},
                    MatchPart[{}, HoldPattern @@ holdPatt,
                        With[{p = Unevaluated @@ holdPatt},
                            patternMatchShift[#1, p]
                        ]
                    ]
                ]
            ],
            patternMatchShift[#2, Unevaluated[head[right]], 1]
        ] &],
        SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0]
    ]
]


(* HoldPattern *)

patternMatch[expr_, patt : Verbatim[HoldPattern][p_]] := patternMatch[Unevaluated[expr], Unevaluated[p]]


(* Verbatim *)

patternMatch[expr_, Verbatim[Verbatim][expr_]] := MatchValues[expr]


(* Except *)

patternMatch[expr_, Verbatim[Except][patt_, t___]] :=
    If[ !PatternMatchQ[Unevaluated[expr], Unevaluated[patt]],
		MatchProduct[
            MatchDefault[Unevaluated[patt]],
            If[ HoldComplete[t] === HoldComplete[],
                MatchValues[expr],
                patternMatch[Unevaluated[expr], Unevaluated[t]]
            ]
        ],
		MatchSum[]
	]


patternMatch[head_Symbol[args___], head_Symbol[left : Verbatim[Except][patt_, t___], right___]] := MatchPart[
    {},
    HoldPattern[head[left, right]],
	LazyMap[Apply[
        MatchProduct[
            MatchPart[{1},
                HoldPattern[left],
                With[{val = Unevaluated @@ head @@@ HoldComplete[#1]},
                    If[ !PatternMatchQ[val, Unevaluated[head[patt]]],
                        MatchProduct[
                            MatchDefault[Unevaluated[head[patt]]],
                            If[ HoldComplete[t] === HoldComplete[],
                                Sequence @@@ MatchValues[#1],
                                patternMatchShift[#1, Unevaluated[head[t]], True]
                            ]
                        ],
                        MatchSum[]
                    ]
                ]
            ],
            patternMatchShift[#2, Unevaluated[head[right]], 1]
        ] &],
        SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0]
    ]
]


(* Alternatives *)

patternMatch[expr_, patt : Verbatim[Alternatives][alts___]] :=
    LazyMap[
        Function[alt, MatchPart[{}, HoldPattern[patt], patternMatch[Unevaluated[expr], Unevaluated[alt]]], HoldAll],
        MatchSum[alts]
    ]

patternMatch[head_Symbol[args___], head_Symbol[left : Verbatim[Alternatives][alts___], right___]] := MatchPart[
    {},
    HoldPattern[head[left, right]],
    LazyMap[Apply[MatchProduct[
        MatchPart[{1},
            HoldPattern[left],
            LazyMap[
                Function[alt, patternMatchShift[#1, Unevaluated[head[alt]], True], HoldAll],
                MatchSum[alts]
            ]
        ],
        patternMatchShift[#2, Unevaluated[head[right]], 1]
    ] &
    ],
        SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0]
    ]
]


(* DefaultAlternatives *)

patternMatch[expr_, patt : Verbatim[DefaultAlternatives][alts___]] :=
    LazyMap[
        With[{alt = Unevaluated @@ Extract[HoldComplete[alts], #, HoldComplete], rest = Drop[HoldComplete[alts], {#}]},
            MatchPart[{}, HoldPattern[patt],
                MatchProduct[
                    With[{names = Cases[alt, Verbatim[Pattern][name_Symbol, _] :> name, All]},
                        MatchPart[{}, head @@@ HoldPattern[rest],
                            MapMatchPart[
                                Replace[MatchPart[_, _[Verbatim[Pattern][name_Symbol, _]], _] /; MemberQ[names, name] :> MatchProduct[]],
                                MatchDefault[rest]
                            ]
                        ]
                    ],
                    patternMatch[Unevaluated[expr], alt]
                ]
            ]
         ] &,
        LazyRange[Length[Unevaluated[patt]], MatchSum]
    ]

patternMatch[head_Symbol[args___], head_Symbol[left : Verbatim[DefaultAlternatives][alts___], right___]] := MatchPart[
    {},
    HoldPattern[head[left, right]],
    LazyMap[Apply[MatchProduct[
        LazyMap[
            Function[n, With[{
                alt = Unevaluated @@ head /@ Extract[HoldComplete[alts], n, HoldComplete],
                rest = Drop[HoldComplete[alts], {n}]
            },
                MatchProduct[
                    MatchPart[{1},
                        HoldPattern[left],
                        MatchProduct[
                            With[{names = Cases[alt, Verbatim[Pattern][name_Symbol, _] :> name, All]},
                                MatchPart[{}, PatternSequence @@@ HoldPattern[rest],
                                    MapMatchPart[
                                        Replace[MatchPart[_, _[Verbatim[Pattern][name_Symbol, _]], match_] /; MemberQ[names, name] :> match],
                                        MatchDefault[rest]
                                    ]
                                ]
                            ],
                            patternMatchShift[#1, alt, True]
                        ]
                    ]
                ]
            ]],
            LazyRange[Length[Unevaluated[left]], MatchSum]
        ],
            patternMatchShift[#2, Unevaluated[head[right]], 1]
    ] &
    ],
        SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0]
    ]
]



(* Optional *)

patternMatch[expr_, patt : Verbatim[Optional][subPatt_, def___]] := MatchPart[
    {},
    HoldPattern[patt],
    MatchSum[
        patternMatch[Unevaluated[expr], Unevaluated[subPatt]],
        MatchDefault[Unevaluated[patt]]
    ]
]


patternMatch[head_Symbol[args___], head_Symbol[left : Verbatim[Optional][patt_, def___], right___]] := MatchPart[
    {},
    HoldPattern[head[left, right]],
	LazyMap[Apply[MatchSum[
        MatchProduct[
            MatchPart[
                {1},
                HoldPattern[left],
                MatchSum[
                    patternMatchShift[#1, Unevaluated[head[patt]], True],
                    If[Length[#1] == 0, MatchDefault[Unevaluated[left]], MatchSum[]]
                ]
            ],
            patternMatchShift[#2, Unevaluated[head[right]], 1]
        ]
        ] &],
        If[Length[HoldComplete[args]] > 0, ReleaseLazyValue @ LazyJoin[LazyReverse[LazyTake[#, 2]], LazyDrop[#, 2]] &, Identity] @
            SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0]
    ]
]


(* Condition *)

patternMatch[expr_, Verbatim[Condition][patt_, cond_]] :=
	LazySelect[MatchExpand @ patternMatch[Unevaluated[expr], Unevaluated[patt]], ReplaceAll[Unevaluated[cond], ReleaseLazyValue @ LazyFirst[MatchBindings[#], {}]] &]


(* PatternTest *)

patternMatch[expr_, Verbatim[PatternTest][patt_, test_]] :=
	LazySelect[MatchExpand @ patternMatch[Unevaluated[expr], Unevaluated[patt]], test @@ ReleaseLazyValue @ LazyFirst[MatchApply[patt, #], Unevaluated[patt]] &]


(* OptionsPattern *)

RepeatedFlatten[expr_] := FixedPoint[FlattenAt[#, Position[#, _List, {1}, Heads -> False]] &, expr]

patternMatch[head_Symbol[args___], head_Symbol[left : _OptionsPattern | _DefaultOptionsPattern, right___]] := With[{
    defaultOpts = Replace[left, {_[] :> Options[head], _[sym_Symbol]:> Options[sym], _[rules : {(_Rule | _RuleDelayed)...}] :> rules, _ :> {}}],
    pattHead = Head[left]
},
    MatchPart[
        {},
        HoldPattern[PatternSequence[left, right]],
        LazyMap[
            Apply[
                MatchProduct[
                    MatchPart[{1},
                        HoldPattern[left],
                        With[{rules = Unevaluated @@ List @@@ (HoldComplete[#] &)[Hold /@
                            If[
                                pattHead === OptionsPattern,
                                RepeatedFlatten[Append[#1, defaultOpts]],
                                With[{opts = RepeatedFlatten[#1]},
                                    If[ AllTrue[opts[[All, 1]], Function[Null, MemberQ[Keys[defaultOpts], Unevaluated[#]], HoldAllComplete]],
                                        Join[opts, HoldComplete @@ defaultOpts],
                                        HoldComplete[Missing[]]
                                    ]
                                ]
                            ]
                        ]},
                            If[ MatchQ[rules, {Hold[(_Rule | _RuleDelayed)]...}],
                                LazyMap[
                                    opts |-> LazyMap[opt |-> Replace[opt, {
                                        Hold[(Rule | RuleDelayed)[key_, value_]] :>
                                            MatchPart[{}, HoldPattern[OptionValue[key]], MatchValues[value]],
                                        _ -> MatchSum[]
                                    }],
                                        MatchSum @@ opts
                                    ],
                                    MatchProduct @@ GatherBy[rules, #[[1, 1]] &]
                                ],
                                MatchSum[]
                            ]
                        ]
                    ],
                    patternMatchShift[#2, Unevaluated[head[right]], 1]
                ] &
            ],
            SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0]
        ]
    ]
]


(* KeyValuePattern *)

patternMatch[expr_, Verbatim[KeyValuePattern][kvalues_]] := patternMatchShift[HoldComplete[expr], HoldComplete[KeyValuePattern[kvalues]], True]

patternMatch[head_Symbol[args___], head_Symbol[left : Verbatim[KeyValuePattern][kvalues_], right___]] := MatchPart[
    {},
    HoldPattern[PatternSequence[left, right]],
    LazyMap[
        Apply[MatchProduct[
            MatchPart[{1},
                HoldPattern[left],
                With[{rules = RepeatedFlatten[#1 /. assoc_Association :> RuleCondition[Normal[assoc]]]},
                    If[ AllTrue[rules, MatchQ[_Rule | _RuleDelayed]],
                        MatchPart[{},
                            HoldPattern[rules],
                            patternMatch[rules, Insert[OrderlessPatternSequence @@@ HoldComplete[kvalues], ___, {1, -1}]]
                        ],
                        MatchSum[]
                    ]
                ]
            ],
            patternMatchShift[#2, Unevaluated[head[right]], 1]
        ] &],
        SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0]
    ]
]


(* IgnoringInactive *)

patternMatch[Inactive[head_][args___], Verbatim[IgnoringInactive][patt_]] := patternMatch[Unevaluated[head[args]], Unevaluated[patt]]
patternMatch[expr_, Verbatim[IgnoringInactive][patt_]] := patternMatch[Unevaluated[expr], Unevaluated[patt]]


(* DeepPattern *)

patternMatch[expr_, Verbatim[DeepPattern][patt_]] := patternMatch[Unevaluated[expr], Unevaluated[patt]]

patternMatch[expr : (head : Except[Sequence])[args___], Verbatim[DeepPattern][patt_]] := MatchPart[{}, HoldPattern[DeepPattern[patt]],
    MatchSum[
        patternMatch[Unevaluated[args], Unevaluated[DeepPattern[patt]]],
        patternMatch[Unevaluated[head], Unevaluated[DeepPattern[patt]]],
        patternMatch[Unevaluated[expr], Unevaluated[patt]]
    ]
]


(* NestedNull *)

patternMatch[expr_, Verbatim[NestedNull][patt_, spec_ : Infinity, lvl_ : 1]] := With[{
    min = Replace[spec, {{k_} :> k, {min_, _} :> min, _ -> 0}],
    max = Replace[spec, {{k_} :> k, {_, max_} :> max}]
},
    If[ max >= min,
        If[ Length[Unevaluated[expr]] > 0,
            With[{arg = Unevaluated @@ Extract[Unevaluated[expr], {1}, HoldComplete]},
                MatchProduct[
                    MatchPart[{}, HoldPattern[patt], patternMatch[Unevaluated[expr], Unevaluated[patt]]],
                    MatchPart[{1}, HoldPattern[NestedNull[patt, spec]], patternMatch[arg, Unevaluated[NestedNull[patt, spec, lvl + 1]]]]
                ]
            ],
            If[0 < min <= lvl <= max, patternMatch[Unevaluated[expr], Unevaluated[patt]], If[min == 0, MatchValues[expr], MatchSum[]]]
        ],
        MatchSum[]
    ]
]


(* Nested *)

patternMatch[expr_, Verbatim[Nested][patt_, spec_ : Infinity]] := With[{
    newSpec = Replace[spec, {k : Except[_List] :> {1, k}}]
},
    patternMatch[Unevaluated[expr], Unevaluated[NestedNull[patt, newSpec]]]
]


(* LazyValue *)

patternMatch[LazyValue[v_], patt_] := MapMatchValues[
    Replace[values_MatchValues :> Map[LazyValue, values]],
    patternMatch[Unevaluated[v], Unevaluated[patt]]
]


(* head cases *)

patternMatch[head_Symbol[], head_Symbol[]] := MatchProduct[]
patternMatch[head_Symbol[__], head_Symbol[]] := MatchSum[]

(* patternMatch[head_Symbol[Longest[same__], args___], head_Symbol[Longest[same__], patt___]] := With[{len = Length[HoldComplete[same]]},
    MatchProduct[
        MatchProduct @@ MapIndexed[Function[Null, MatchPart[#2, HoldPattern[#1], MatchValues[#1]], HoldAllComplete], Unevaluated[{same}]],
        MapMatchPart[
            Replace[MatchPart[{p : Except[0], part___}, rest___] :> MatchPart[{p + len, part}, rest]],
            patternMatch[Unevaluated[head[args]], Unevaluated[head[patt]]]
        ]
    ]
] *)

patternMatch[head_Symbol[args___], head_Symbol[patt__]] := MatchPart[{}, HoldPattern[head[patt]], ToLazyList[LazyMap[
    MatchProduct @@ With[{vs = Flatten /@ HoldComplete @@@ Normal[#]},
        MapThread[
            With[{v = Unevaluated @@ #1, p = Unevaluated @@ #2},
                (* EchoFunction[ResourceFunction["PrettyForm"][{v, h[patt]}], MatchBindings /* Normal]@ *)
                MatchPart[{#3}, HoldPattern @@ #2, patternMatch[v, p]]
                (* MatchPart[{#3}, HoldPattern @@ #2, MapMatchPart[Replace[MatchPart[{p : Except[0], ps___}, rest___] :> MatchPart[{p, ps}, rest]], patternMatch[v, p]]] *)
            ] &,
            {vs, List @@ HoldComplete /@ HoldComplete[patt], Range[Length[vs]]}
        ]
    ] &,
    LazySplits[HoldComplete /@ Unevaluated[{args}], Length[HoldComplete[patt]]]
], MatchSum]]

patternMatch[head1_[args___], head2_[patt___]] := MatchProduct[
    MatchPart[{0}, HoldPattern[head2], patternMatch[Unevaluated[head1], Unevaluated[head2]]],
    patternMatchShift[HoldComplete[args], HoldComplete[patt]]
]

patternMatch[expr_, expr_] := MatchValues[expr]


patternMatch[___] := MatchSum[]


PatternMatch[expr_, patt_] := Match[patternMatch[Unevaluated[expr], Unevaluated[patt]]]

