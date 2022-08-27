Package["Wolfram`Patterns`"]

PackageImport["Wolfram`Lazy`"]

PackageExport["PatternMatch"]
PackageExport["SequenceSplits"]
PackageExport["ShortestTriples"]
PackageExport["LongestTriples"]
PackageExport["ShiftPatternMatch"]
PackageExport["MapMatchPart"]



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
MapMatchPart[f_, match_MatchPart] := f[match]
MapMatchPart[_, match_MatchValues] := match
MapMatchPart[f_, LazyValue[v_]] := MapMatchPart[f, v]

MapMatchValues[f_, matches : _MatchSum | _MatchProduct] := LazyMap[MapMatchValues[f, #] &, matches]
MapMatchValues[f_, MatchPart[part_, patt_, match_]] := MatchPart[part, f[patt], MapMatchValues[f, match]]
MapMatchValues[f_, match_MatchValues] := f[match]
MapMatchValues[f_, LazyValue[v_]] := MapMatchValues[f, v]


flattenIdentities[expr_] := FlattenAt[expr, Position[expr, _[_], {1}, Heads -> False]]


ShiftPatternMatch[seq_HoldComplete, head_Symbol[patt___], shift : _Integer ? NonNegative : 0, drop : True | False : False] := With[{
    val = Unevaluated @@ head @@@ HoldComplete[seq]
},
    MapMatchPart[
        Replace[{
            MatchPart[{0, ___}, ___] :> MatchProduct[],
            If[ drop,
                MatchPart[{_, ps___}, rest___] :> MatchPart[{ps}, rest],
                If[shift > 0, MatchPart[{p_, ps___}, rest___] :> MatchPart[{p + shift, ps}, rest], Nothing]
            ]
        }],
        PatternMatch[val, Unevaluated[head[patt]]]
    ]
]


(* PatternMatch *)

SetAttributes[PatternMatch, SequenceHold]

Off[Pattern::patv]


(* OneIdentity *)

PatternMatch[expr : Except[head_Symbol[___]], head_Symbol[patt___]] /; MemberQ[Attributes[head], OneIdentity] :=
    PatternMatch[Unevaluated[head[expr]], Unevaluated[head[patt]]]


(* Orderless *)

PatternMatch[head_Symbol[args___], head_Symbol[patt___]] /;
    Not[Length[Unevaluated[{patt}]] == 1 && Head[Unevaluated[patt]] === OrderlessPatternSequence] && MemberQ[Attributes[head], Orderless] :=
    Module[{h},
        DefaultValues[h] = DefaultValues[head] /. head :> h;
        SetAttributes[h, DeleteCases[Attributes[head], Orderless]];
        MapMatchValues[
            ReplaceAll[h :> head],
            MapMatchPart[
                Replace[MatchPart[{1}, _, match_] :> match],
                PatternMatch[Unevaluated[h[args]], Unevaluated[h[OrderlessPatternSequence[patt]]]]
            ]
        ]
    ]


(* Shortest *)

PatternMatch[Sequence[args___], Verbatim[Shortest][patt_]] :=
    PatternMatch[Unevaluated[Sequence[args]], Unevaluated[Sequence[Shortest[patt]]]]

PatternMatch[head_Symbol[args___], head_Symbol[left___, mid : Verbatim[Shortest][patt_], right___]] := With[{
    l = Length[Hold[left]], r = Length[Hold[right]]
},
    LazyMap[Apply[
        If[ l == 0 && Length[#1] > 0 || r == 0 && Length[#3] > 0,
            MatchSum[],
            MatchProduct[
                If[ l == 0,
                    MatchProduct[],
                    ShiftPatternMatch[#1, Unevaluated[head[left]]]
                ],
                MatchPart[{l + 1},
                    HoldPattern[mid],
                    ShiftPatternMatch[#2, Unevaluated[head[patt]], l]
                ],
                If[ r == 0,
                    MatchProduct[],
                    ShiftPatternMatch[#3, Unevaluated[head[right]], l + 1]
                ]
            ]
        ] &
    ],
        ShortestTriples[HoldComplete[args]]
    ]
]


(* Longest *)

PatternMatch[Sequence[args___], Verbatim[Longest][patt_]] :=
    PatternMatch[Unevaluated[Sequence[args]], Unevaluated[Sequence[Longest[patt]]]]

PatternMatch[head_Symbol[args___], head_Symbol[left___, mid : Verbatim[Longest][patt_], right___]] := With[{
    l = Length[HoldComplete[left]], r = Length[HoldComplete[right]]
},
    LazyMap[Apply[
        If[ l == 0 && Length[#1] > 0 || r == 0 && Length[#3] > 0,
            MatchSum[],
            MatchProduct[
                If[ l == 0,
                    MatchProduct[],
                    ShiftPatternMatch[#1, Unevaluated[head[left]]]
                ],
                MatchPart[{l + 1},
                    HoldPattern[mid],
                    ShiftPatternMatch[#2, Unevaluated[head[patt]], l]
                ],
                If[ r == 0,
                    MatchProduct[],
                    ShiftPatternMatch[#3, Unevaluated[head[right]], l + 1]
                ]
            ]
        ] &
    ],
        LongestTriples[HoldComplete[args]]
    ]
]


(* OrderlessPatternSequence *)

PatternMatch[Sequence[args___], Verbatim[OrderlessPatternSequence][patt___]] :=
    PatternMatch[Unevaluated[Sequence[args]], Unevaluated[Sequence[OrderlessPatternSequence[patt]]]]

PatternMatch[arg_, Verbatim[OrderlessPatternSequence][patt___]] :=
    PatternMatch[Unevaluated[Sequence[arg]], Unevaluated[Sequence[OrderlessPatternSequence[patt]]]]

PatternMatch[head_Symbol[args___], head_Symbol[left : Verbatim[OrderlessPatternSequence][patt___], right___]] :=
    LazyMap[Apply[
        MatchProduct[
            MatchPart[{1}, HoldPattern[left],
                LazyMap[
                    ShiftPatternMatch[#, Unevaluated[head[patt]]] &,
                    ToLazyList[LazyPermutations[#1], MatchSum]
                ]
            ],
            ShiftPatternMatch[#2, Unevaluated[head[right]], 1]
        ] &],
		SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0]
	]


(* PatternSequence *)

PatternMatch[Sequence[args___], Verbatim[PatternSequence][patt___]] :=
    PatternMatch[Unevaluated[Sequence[args]], Unevaluated[Sequence[patt]]]

PatternMatch[arg_, Verbatim[PatternSequence][patt___]] :=
    PatternMatch[Unevaluated[Sequence[arg]], Unevaluated[Sequence[patt]]]

PatternMatch[head_Symbol[args___], head_Symbol[left : Verbatim[PatternSequence][patt___], right___]] :=
    LazyMap[Apply[
        MatchProduct[
            MatchPart[{1}, HoldPattern[left],
                ShiftPatternMatch[#1, Unevaluated[head[patt]]]
            ],
            ShiftPatternMatch[#2, Unevaluated[head[right]], 1]
        ] &],
		SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0]
	]


(* Flat *)

PatternMatch[head_Symbol[args___], head_Symbol[patt__]] /; MemberQ[Attributes[head], Flat] := Module[{h},
    DefaultValues[h] = DefaultValues[head] /. head :> h;
    SetAttributes[h, DeleteCases[Attributes[head], Flat]];
    MatchPart[{}, HoldPattern[head[patt]], MapMatchValues[
        ReplaceAll[h :> head],
        LazyMap[
            With[{v = If[MemberQ[Attributes[head], OneIdentity], flattenIdentities, Identity][h @@@ HoldComplete @@ Flatten /@ HoldComplete @@@ Normal[#]]},
                (* EchoFunction[ResourceFunction["PrettyForm"][{v, h[patt]}], MatchBindings /* Normal]@ *)
                ShiftPatternMatch[v, Unevaluated[h[patt]]]
            ] &,
            LazySplits[HoldComplete /@ Unevaluated[{args}], Length[HoldComplete[patt]], MatchSum]
        ]
    ]]
]


(* Pattern *)

PatternMatch[expr_, patt : Verbatim[Pattern][_Symbol, subPatt_]] :=
	MatchPart[{}, HoldPattern[patt], PatternMatch[Unevaluated[expr], Unevaluated[subPatt]]]

PatternMatch[head_Symbol[args___], head_Symbol[left : Verbatim[Pattern][_Symbol, patt_], right___]] :=
    LazyMap[Apply[
        MatchProduct[
            MatchPart[{1},
                HoldPattern[left],
                ShiftPatternMatch[#1, Unevaluated[head[patt]], True]
            ],
            ShiftPatternMatch[#2, Unevaluated[head[right]], 1]
        ] &],
        SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0]
    ]


(* Blank *)

PatternMatch[expr_, Verbatim[Blank][]] := MatchValues[expr]

PatternMatch[expr_, Verbatim[Blank][h_]] := With[{head = Unevaluated @@ Head[Unevaluated[expr], HoldComplete]},
	MatchProduct[PatternMatch[head, h], MatchValues[expr]]]

PatternMatch[head_Symbol[args___], head_Symbol[left : Verbatim[Blank][h___], right___]] :=
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
            ShiftPatternMatch[#2, Unevaluated[head[right]], 1]
        ] &],
        If[ MemberQ[Attributes[head], Flat], Identity, LazySelect[#, MatchQ[#[[1]], HoldComplete[_h]] &] &] @
            SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0]
    ]


(* BlankSequence *)

PatternMatch[Sequence[args___], Verbatim[BlankSequence][h___]] :=
    If[ MatchQ[HoldComplete[args], HoldComplete[__h]],
	    MatchValues[Sequence[args]],
        MatchSum[]
    ]

PatternMatch[arg_, Verbatim[BlankSequence][h___]] :=
    If[ MatchQ[HoldComplete[arg], HoldComplete[_h]],
	    MatchValues[arg],
        MatchSum[]
    ]

PatternMatch[head_Symbol[args__], head_Symbol[left : Verbatim[BlankSequence][h___], right___]] :=
	LazyMap[Apply[
        MatchProduct[
            MatchPart[{1}, HoldPattern[left], HoldApply[Sequence, #1, MatchValues]],
            ShiftPatternMatch[#2, Unevaluated[head[right]], 1]
        ] &],
		LazySelect[
			SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0],
			MatchQ[#[[1]], HoldComplete[__h]] &
		]
	]


(* BlankNullSequence *)

PatternMatch[Sequence[args___], Verbatim[BlankNullSequence][h___]] :=
    If[ MatchQ[HoldComplete[args], HoldComplete[___h]],
	    MatchValues[Sequence[args]],
        MatchSum[]
    ]

PatternMatch[arg_, Verbatim[BlankNullSequence][h___]] :=
    If[ MatchQ[HoldComplete[arg], HoldComplete[_h]],
	    MatchValues[arg],
        MatchSum[]
    ]

PatternMatch[head_Symbol[args___], head_Symbol[left : Verbatim[BlankNullSequence][h___], right___]] :=
	LazyMap[Apply[
        MatchProduct[
            MatchPart[{1}, HoldPattern[left], HoldApply[Sequence, #1, MatchValues]],
            ShiftPatternMatch[#2, Unevaluated[head[right]], 1]
        ] &],
		LazySelect[
			SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0],
			MatchQ[#[[1]], HoldComplete[___h]] &
		]
	]


(* RepeatedNull *)

PatternMatch[head_Symbol[args___], head_Symbol[left : Verbatim[RepeatedNull][patt_, spec_ : Infinity], right___]] := With[{
    min = Replace[spec, {{k_} :> k, {min_, _} :> min, _ -> 0}],
    max = Replace[spec, {{k_} :> k, {_, max_} :> max}]
},
With[{
    numRepeats = max - min + 1
},
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
                                        ShiftPatternMatch[r, Unevaluated[head[right]], Max[i - 1, 0]]
                                    ],
                                    #[[2]], #[[3]] + 1}], LazyList[]],
                                (* last iteration but input is not empty *)
                                i == numRepeats,
                                LazyList[],
                                True,
                                Block[{subst = LazyListToList @ MatchExpand @ PatternMatch[val, p]}, LazySelect[# =!= Nothing &] @ LazyMap[
                                    With[{next = HoldComplete @@ Lookup[ReleaseLazyValue @ LazyFirst[MatchBindings[#], <||>], rest, Null, Hold]},
                                        If[ next =!= Null && Length[next] <= len,
                                            {
                                                MatchProduct[
                                                    prevSubst,
                                                    MapMatchPart[
                                                        Replace[{
                                                            (* replace with dummy sequence *)
                                                            MatchPart[{restPos}, __] -> MatchProduct[],
                                                            MatchPart[{p_, ps___}, rest___] :> MatchPart[{If[i == 0, p, i], ps}, rest]
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
]]


(* Repeated *)

PatternMatch[head_Symbol[args___], head_Symbol[Verbatim[Repeated][patt_, spec_ : Infinity], right___]] := With[{
    newSpec = Replace[spec, {k : Except[_List] :> {1, k}}]
},
    PatternMatch[Unevaluated[head[args]], Unevaluated[head[RepeatedNull[patt, newSpec], right]]]
]


(* HoldPattern *)

PatternMatch[expr_, Verbatim[HoldPattern][patt_]] := PatternMatch[Unevaluated[expr], Unevaluated[patt]]


(* Verbatim *)

PatternMatch[expr_, Verbatim[Verbatim][expr_]] := MatchValues[expr]


(* Except *)

PatternMatch[expr_, Verbatim[Except][patt_, t___]] :=
    If[ !PatternMatchQ[Unevaluated[expr], Unevaluated[patt]],
		MatchProduct[
            MatchDefault[Unevaluated[patt]],
            If[ HoldComplete[t] === HoldComplete[],
                MatchValues[expr],
                PatternMatch[Unevaluated[expr], Unevaluated[t]]
            ]
        ],
		MatchSum[]
	]


PatternMatch[head_Symbol[args___], head_Symbol[left : Verbatim[Except][patt_, t___], right___]] :=
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
                                ShiftPatternMatch[#1, Unevaluated[head[t]], True]
                            ]
                        ],
                        MatchSum[]
                    ]
                ]
            ],
            ShiftPatternMatch[#2, Unevaluated[head[right]], 1]
        ] &],
        SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0]
    ]


(* Alternatives *)

PatternMatch[expr_, patt : Verbatim[Alternatives][alts___]] :=
    LazyMap[
        Function[alt, MatchPart[{}, HoldPattern[patt], PatternMatch[Unevaluated[expr], Unevaluated[alt]]], HoldAll],
        MatchSum[alts]
    ]

PatternMatch[head_Symbol[args___], head_Symbol[left : Verbatim[Alternatives][alts___], right___]] :=
    LazyMap[Apply[MatchProduct[
        MatchPart[{1},
            HoldPattern[left],
            LazyMap[
                Function[alt, ShiftPatternMatch[#1, Unevaluated[head[alt]], True], HoldAllComplete],
                MatchSum[alts]
            ]
        ],
        ShiftPatternMatch[#2, Unevaluated[head[right]], 1]
    ] &], SequenceSplits[HoldComplete[args]]
    ]



(* Optional *)

PatternMatch[expr_, Verbatim[Optional][patt_, def___]] := MatchSum[
    PatternMatch[Unevaluated[expr], Unevaluated[patt]],
    MatchPart[
        {},
        Replace[HoldPattern[patt], Verbatim[HoldPattern][Verbatim[Optional][p_Pattern, ___]] :> HoldPattern[p]],
        If[HoldComplete[def] === HoldComplete[], MatchValues[Sequence[]], MatchValues[def]]
    ],
    MatchDefault[Unevaluated[patt]]
]


PatternMatch[head_Symbol[args___], head_Symbol[left : Verbatim[Optional][patt_, def___], right___]] :=
	LazyMap[Apply[
        MatchProduct[
            MatchSum[
                MatchPart[
                    {1},
                    HoldPattern[left],
                    ShiftPatternMatch[#1, Unevaluated[head[patt]], True]
                ],
                MatchDefault[Unevaluated[head[left]]]
            ],
            ShiftPatternMatch[#2, Unevaluated[head[right]], 1]
        ] &],
        (* If[ MemberQ[Attributes[head], Flat], Identity, LazySelect[#, MatchQ[#[[1]], HoldComplete[_]] &] &] @ *)
            SequenceSplits[HoldComplete[args], Length[HoldComplete[right]] == 0]
    ]


(* Condition *)

PatternMatch[expr_, Verbatim[Condition][patt_, cond_]] :=
	LazySelect[MatchExpand @ PatternMatch[Unevaluated[expr], Unevaluated[patt]], ReplaceAll[Unevaluated[cond], ReleaseLazyValue @ LazyFirst[MatchBindings[#], {}]] &]


(* PatternTest *)

PatternMatch[expr_, Verbatim[PatternTest][patt_, test_]] :=
	LazySelect[MatchExpand @ PatternMatch[Unevaluated[expr], Unevaluated[patt]], test @@ ReleaseLazyValue @ LazyFirst[MatchApply[patt, #], Unevaluated[patt]] &]


(* head cases *)

PatternMatch[head_Symbol[], head_Symbol[]] := MatchProduct[]
PatternMatch[head_Symbol[__], head_Symbol[]] := MatchSum[]

(* PatternMatch[head_Symbol[Longest[same__], args___], head_Symbol[Longest[same__], patt___]] := With[{len = Length[HoldComplete[same]]},
    MatchProduct[
        MatchProduct @@ MapIndexed[Function[Null, MatchPart[#2, HoldPattern[#1], MatchValues[#1]], HoldAllComplete], Unevaluated[{same}]],
        MapMatchPart[
            Replace[MatchPart[{p : Except[0], part___}, rest___] :> MatchPart[{p + len, part}, rest]],
            PatternMatch[Unevaluated[head[args]], Unevaluated[head[patt]]]
        ]
    ]
] *)

PatternMatch[head_Symbol[args___], head_Symbol[patt__]] := LazyMap[
    MatchProduct @@ With[{vs = Flatten /@ HoldComplete @@@ Normal[#]},
        MapThread[
            With[{v = Unevaluated @@ #1, p = Unevaluated @@ #2},
                (* EchoFunction[ResourceFunction["PrettyForm"][{v, h[patt]}], MatchBindings /* Normal]@ *)
                MatchPart[{#3}, HoldPattern @@ #2, PatternMatch[v, p]]
            ] &,
            {vs, List @@ HoldComplete /@ HoldComplete[patt], Range[Length[vs]]}
        ]
    ] &,
    LazySplits[HoldComplete /@ Unevaluated[{args}], Length[HoldComplete[patt]], MatchSum]
]

PatternMatch[head1_[args___], head2_[patt___]] := MatchProduct[
    MapMatchPart[
        Replace[MatchPart[part_, rest__] :> MatchPart[Prepend[part, 0], rest]],
        PatternMatch[Unevaluated[head1], Unevaluated[head2]]
    ],
    PatternMatch[HoldComplete[args], HoldComplete[patt]]
]

PatternMatch[expr_, expr_] := MatchValues[expr]


PatternMatch[___] := MatchSum[]

