Package["WolframInstitute`Gravitas`ShapedTensor`"]

PackageExport[DimensionQ]
PackageExport[Dimension]

PackageScope[DimensionName]
PackageScope[DimensionSymbol]



DimensionName[i_Integer ? Positive, alphabet : {__}] := Block[{
    n = Length[alphabet],
    j, k
}, 
    j = Mod[i - 1, n] + 1;
    k = Quotient[i - 1, n];
    ToString[alphabet[[j]]] <> If[k > 0, ToString[k], ""]
]

DimensionName[i_, Automatic] := DimensionName[i, CharacterRange["i", "z"]]

DimensionName[i_] := DimensionName[i, Automatic]


CanonicalSymbolName[s_Symbol ? AtomQ] := With[{t = Unevaluated @@ ResourceFunction["UnformalizeSymbols"][s, "DeferQ" -> True]}, SymbolName[t]]

CanonicalSymbolName[s_] := s



DimensionQ[Dimension[_Integer, ___]] := True

DimensionQ[___] := False


Dimension[Dimension[d_, ___], args___] := Dimension[d, args]


Dimension["Properties"] = Sort @ {
    "SignedDimension", "Dimension", "Size", "Name", "Indices",
    "Properties"
}

(d_Dimension ? DimensionQ)[prop_String, args___] := Prop[d, prop, args]

Prop[Dimension[d_, ___], "SignedDimension"] := d

Prop[d_, "Dimension" | "Size"] := Abs[d["SignedDimension"]]

Prop[Dimension[_, name_ : "i", ___], "Name"] := CanonicalSymbolName[name]

Prop[Dimension[d_, name_ : "i", indices : {___} : {}, ___], "Indices"] :=
    Join[indices, Array[Subscript[name, #] &, Abs[d] - Length[indices], Length[indices] + 1]]


DimensionSymbol[d_, name_] := 
    Which[d > 0, OverBar[name], d < 0, UnderBar[name], True, Style[name, Opacity[.3]]]

Prop[d_, "Symbol"] := DimensionSymbol[d["SignedDimension"], d["Name"]]

Prop[d_, "View", limit_Integer : 10] := With[{dim = d["Dimension"]},
    If[dim > limit, dim, Row[{dim, " : ", Row[d["Indices"], ","]}]]
]

Prop[_, prop_String, ___] := Missing[prop]


Dimension /: MakeBoxes[d_Dimension ? DimensionQ, form_] := With[{
    box = ToBoxes[d["Symbol"], form],
    tooltip = ToBoxes[d["View"], form]
},
    InterpretationBox[box, d, Tooltip -> tooltip]
]

