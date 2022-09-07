
Package["Wolfram`Patterns`"]

PackageImport["Wolfram`Lazy`"]

PackageExport["NameValuePattern"]



NameValuePattern[args : _Pattern..., kwargs : PatternSequence[(Optional | Rule)[_Pattern, _]...]] :=
    PatternSequence[
        PatternSequence @@ Replace[#1, {
            _[Verbatim[Pattern][name_Symbol, p_], def_] :> Optional[Pattern @@ Hold[name, Except[_Rule, p]], def],
            Verbatim[Pattern][name_Symbol, p_] :> Pattern @@ Hold[name, Except[_Rule, p]]
        },
            {1}
        ],
        OrderlessPatternSequence @@ Replace[#2, {
            _[p : Verbatim[Pattern][name_Symbol, _], def_] :> Optional[name -> Optional[p, def]],
            p : Verbatim[Pattern][name_Symbol, _] :> name -> p
        },
            {1}
        ]
    ] & @@@ Alternatives @@ NormalLazy @ LazySplitsReverse[{args, kwargs}] //. {
        (Alternatives | PatternSequence | OrderlessPatternSequence | AlternativesSequence)[] -> Sequence[],
        (Alternatives | PatternSequence | OrderlessPatternSequence | AlternativesSequence)[x_] :> x,
        (h : PatternSequence | OrderlessPatternSequence)[left___, h_[mid___], right___] :> h[left, mid, right],
        (PatternSequence | OrderlessPatternSequence)[(PatternSequence | OrderlessPatternSequence)[mid___]] :> OrderlessPatternSequence[mid]
        }

