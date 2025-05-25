Package["WolframInstitute`Gravitas`"]

PackageExport[MetricTensorQ]
PackageExport[MetricTensor]



(* Validation *)

metricTensorQ[MetricTensor[m_ ? SquareMatrixQ, coordinates_ ? VectorQ, {_ ? BooleanQ, _ ? BooleanQ}]] :=
    Length[m] == Length[coordinates]

metricTensorQ[___] := False


MetricTensorQ[m_MetricTensor] := System`Private`HoldValidQ[m] || metricTensorQ[Unevaluated[m]]

MetricTensorQ[___] := False


(* Built-in metrics *)

MetricTensor[] := {
    "Symmetric", "SymmetricField", "Asymmetric", "AsymmetricField",
    "Euclidean", "Minkowski", 
    "Schwarzschild", "IsotropicSchwarzschild",
    "EddingtonFinkelstein", "IngoingEddingtonFinkelstein", "OutgoingEddingtonFinkelstein",
    "GullstrandPainleve", "IngoingGullstrandPainleve", "OutgoingGullstrandPainleve", 
    "KruskalSzekeres", "Kerr", "ReissnerNordstrom", "KerrNewman", "Godel", "FLRW"
}

t = \[FormalT]
x = \[FormalX]
y = \[FormalY]
z = \[FormalZ]
r = \[FormalR]
T = \[FormalCapitalT]
X = \[FormalCapitalX]
theta = \[FormalTheta]
phi = \[FormalPhi]
M = \[FormalCapitalM]
Q = \[FormalCapitalQ]
J = \[FormalCapitalJ]
k = \[FormalK]
a = \[FormalA]
sqrt2 = \[Sqrt]2
omega = \[FormalOmega]
u = \[FormalU]
v = \[FormalV]

g = \[FormalG]
mu = \[FormalMu]
nu = \[FormalNu]


padCoordinates[coordinates_List, d_Integer ? Positive] := PadRight[Join[coordinates, Superscript[x, #] & /@ Range[d - Length[coordinates]]], d]

padCoordinates[Automatic, d_] := padCoordinates[{}, d]


(* Symmetric *)

MetricTensor["Symmetric"[d : _Integer ? Positive : 4], args___] := 
    MetricTensor[
        SymmetrizedArray[(# -> Subscript[g, #] &) /@ Select[Tuples[Range[d], 2], OrderedQ], {d, d}, Symmetric[{1, 2}]],
        args
    ]


(* SymmetricField *)

MetricTensor["SymmetricField"[d : _Integer ? Positive : 4], coordinates_ : Automatic, args___] := With[{
    xs = padCoordinates[coordinates, d]
},
    MetricTensor[
        SymmetrizedArray[(# -> Subscript[g, #] @@ xs &) /@ Select[Tuples[Range[d], 2], OrderedQ], {d, d}, Symmetric[{1, 2}]],
        xs,
        args
    ]
]


(* Asymmetric *)

MetricTensor["Asymmetric"[d : _Integer ? Positive : 4], args___] := 
    MetricTensor[
        SymmetrizedArray[(# -> Subscript[g, #] &) /@ Subsets[Range[d], {2}], {d, d}, Antisymmetric[{1, 2}]],
        args
    ]


(* AsymmetricField *)

MetricTensor["AsymmetricField"[d : _Integer ? Positive : 4], coordinates_ : Automatic, args___] :=  With[{
    xs = padCoordinates[coordinates, d]
},
    MetricTensor[
        SymmetrizedArray[(# -> Subscript[g, #] @@ xs &) /@ Subsets[Range[d], {2}], {d, d}, Antisymmetric[{1, 2}]],
        xs,
        args
    ]
]

(* Euclidean *)

MetricTensor["Euclidean"[d : _Integer ? Positive : 3], args___] := 
    MetricTensor[DiagonalMatrix[ConstantArray[1, d]], args]


(* Minkowski *)

MetricTensor["Minkowski"[d : _Integer ? Positive : 4], coordinates_ : Automatic, args___] := 
    MetricTensor[
        DiagonalMatrix[Join[{-1}, ConstantArray[1, d - 1]]],
        Replace[coordinates, Automatic :> Join[{t}, Superscript[x, #] & /@ Range[d - 1]]],
        args
    ]


(* Schwarzschild *)

MetricTensor["Schwarzschild"[M_ : M], {t_ : t, r_ : r, theta_ : theta, phi_ : phi}, args___] := 
    MetricTensor[
        DiagonalMatrix[{ - (1 - (2 * M) / r), 1 / (1 - (2 * M) / r), r ^ 2, r ^ 2 * Sin[theta] ^ 2}],
        {t, r, theta, phi},
        args
    ]


(* IsotropicSchwarzschild *)

MetricTensor["IsotropicSchwarzschild"[M_ : M], {t_ : t, r_ : r, theta_ : theta, phi_ : phi}, args___] := With[{
    f = (1 - M / (2 * r)) / (1 + m / (2 * r))
},
    MetricTensor[
        DiagonalMatrix[{- f ^ 2, (1 + M / (2 * r)) ^ 4, r ^ 2, r ^ 2 * Sin[theta] ^ 2}],
        {t, r, theta, phi},
        args
    ]
]


(* EddingtonFinkelstein *)

MetricTensor["EddingtonFinkelstein"[M_ : M], {t_ : t, r_ : r, theta_ : theta, phi_ : phi}, args___] := 
    MetricTensor[
        {
            {- (1 - (2 * M) / r), 1, 0, 0},
            {1, 0, 0, 0},
            {0, 0, r ^ 2, 0},
            {0, 0, 0, r ^ 2 * Sin[theta] ^ 2}
        },
        {t, r, theta, phi},
        args
    ]


(* GullstrandPainleve *)

MetricTensor["GullstrandPainleve"[M_ : M], {t_ : t, r_ : r, theta_ : theta, phi_ : phi}, args___] := 
    MetricTensor[
        {
            {- (1 - (2 * M) / r), Sqrt[2 * M / r], 0, 0},
            {Sqrt[2 * M / r], 1, 0, 0},
            {0, 0, r ^ 2, 0},
            {0, 0, 0, r ^ 2 * Sin[theta] ^ 2}
        },
        {t, r, theta, phi},
        args
    ]


(* KruskalSzekeres *)

MetricTensor["KruskalSzekeres"[M_ : M], {T_ : T, X_ : X, theta_ : theta, phi_ : phi}, args___] := With[{
    r = 2 * M / (1 - u * v)
},
    MetricTensor[
        {
            {- (32 * M ^ 3 * Exp[-r / (2 * M)]) / r, 0, 0, 0},
            {0, (32 * M ^ 3 * Exp[-r / (2 * M)]) / r, 0, 0},
            {0, 0, r ^ 2, 0},
            {0, 0, 0, r ^ 2 * Sin[theta] ^ 2}
        },
        {T, X, theta, phi},
        args
    ]
]


(* Kerr *)

MetricTensor["Kerr"[M_ : M, J_ : J], {t_ : t, r_ : r, theta_ : theta, phi_ : phi}, args___] := With[{
    rho = r ^ 2 + (J * Cos[theta]) ^ 2, delta = r ^ 2 - (2 * M * r) + J ^ 2
},
    MetricTensor[
        {
            {- 1 + (2 * M * r) / rho, 0, 0, - (2 * M * r * J * Sin[theta] ^ 2) / rho},
            {0, rho / delta, 0, 0},
            {0, 0, rho, 0},
            {- (2 * M * r * J * Sin[theta] ^ 2) / rho, 0, 0, 
                (r ^ 2 + J ^ 2 + (2 * M * r * J ^ 2 * Sin[theta] ^ 2) / rho) * Sin[theta] ^ 2}
        },
        {t, r, theta, phi},
        args
    ]
]


(* ReissnerNordstrom *)

MetricTensor["ReissnerNordstrom"[m_ : m, q_ : q], {t_ : t, r_ : r, theta_ : theta, phi_ : phi}, args___] := With[{
    f = 1 - (2 * m) / r + (q ^ 2) / (r ^ 2)
},
    MetricTensor[
        DiagonalMatrix[{- f, 1 / f, r ^ 2, r ^ 2 * Sin[theta] ^ 2}],
        {t, r, theta, phi},
        args
    ]
]


(* KerrNewman *)

MetricTensor["KerrNewman"[m_ : m, q_ : q, j_ : j], {t_ : t, r_ : r, theta_ : theta, phi_ : phi}, args___] := With[{
    rho = r ^ 2 + (j * Cos[theta]) ^ 2, delta = r ^ 2 - (2 * m * r) + j ^ 2 - (q ^ 2)
},
    MetricTensor[
        {
            {- 1 + (2 * m * r) / rho, 0, 0, - (2 * m * r * j * Sin[theta] ^ 2) / rho},
            {0, rho / delta, 0, 0},
            {0, 0, rho, 0},
            {- (2 * m * r * j * Sin[theta] ^ 2) / rho, 0, 0, 
                (r ^ 2 + j ^ 2 + (2 * m * r * j ^ 2 * Sin[theta] ^ 2) / rho) * Sin[theta] ^ 2}
        },
        {t, r, theta, phi},
        args
    ]
]


(* Godel *)

MetricTensor["Godel"[omega_ : omega], {t_ : t, x_ : x, y_ : y, z_ : z}, args___] := 
    MetricTensor[
        {
            {- 1, Exp[2 * sqrt2 * omega * x] / 2, 0, 0},
            {Exp[2 * sqrt2 * omega * x] / 2, 1, 0, 0},
            {0, 0, 1, 0},
            {0, 0, 0, 1}
        },
        {t, x, y, z},
        args
    ]


(* FLRW *)

MetricTensor["FLRW"[k_ : k, a_ : a], {t_ : t, r_ : r, theta_ : theta, phi_ : phi}, args___] := With[{
    at = a[t]
},
    MetricTensor[
        DiagonalMatrix[{- 1, at ^ 2 / (1 - k * r ^ 2), at ^ 2 * r ^ 2, at ^ 2 * r ^ 2 * Sin[theta] ^ 2}],
        {t, r, theta, phi},
        args
    ]
]


(* General constructors *)

MetricTensor[name_String, args___] := MetricTensor[name[], args]

MetricTensor[name : _String[___]] := MetricTensor[name, {}]

MetricTensor[{name_String, params___}, args___] := MetricTensor[name[params], args]

MetricTensor[matrix_ ? SquareMatrixQ] := MetricTensor[matrix, Superscript[x, #] & /@ Range[Length[matrix]]]

MetricTensor[vector_ ? VectorQ] := MetricTensor[DiagonalMatrix[vector]]


m : MetricTensor[matrix_, coordinates_, i : _ ? BooleanQ : True, j : _ ? BooleanQ : True] := 
    MetricTensor[matrix, coordinates, {i, j}]

m_MetricTensor /; System`Private`HoldNotValidQ[m] && metricTensorQ[Unevaluated[m]] :=
    System`Private`SetNoEntry[System`Private`HoldSetValid[m]]


(* Mutation *)

MetricTensor[mt_MetricTensor, coordinates_List] := MetricTensor[mt["Matrix"], padCoordiantes[coordinates, mt["Dimension"]], mt["Indices"]]

MetricTensor[mt_MetricTensor, i_ ? BooleanQ] := MetricTensor[mt["Matrix"], mt["Coordinates"], i, mt["Indices"][[2]]]

MetricTensor[mt_MetricTensor, i_ ? BooleanQ, j_ ? BooleanQ] := MetricTensor[mt["Matrix"], mt["Coordinates"], i, j]


(* Properties *)

(m_MetricTensor ? MetricTensorQ)[prop_String | prop_String[args___]] := Prop[m, prop, args]

MetricTensor["Properties"] = {
    "MatrixRepresentation", "ReducedMatrixRepresentation", "Coordinates", "CoordinateOneForms", "Indices", "CovariantQ", 
    "ContravariantQ", "MixedQ", "Symbol", "Dimensions", "SymmetricQ", "DiagonalQ", "Signature", "RiemannianQ", 
    "PseudoRiemannianQ", "LorentzianQ", "RiemannianConditions", "PseudoRiemannianConditions", "LorentzianConditions", 
    "MetricSingularities", "Determinant", "ReducedDeterminant", "Trace", "ReducedTrace", "Eigenvalues", 
    "ReducedEigenvalues", "Eigenvectors", "ReducedEigenvectors", "MetricTensor", "InverseMetricTensor", "LineElement", 
    "ReducedLineElement", "VolumeForm", "ReducedVolumeForm", "TimelikeQ", "LightlikeQ", "SpacelikeQ", 
    "LengthPureFunction", "AnglePureFunction", "Properties"
}


Prop[MetricTensor[m_, _, _] ? MetricTensorQ, "Matrix" | "Tensor"] := m

Prop[MetricTensor[_, coordinates_, _] ? MetricTensorQ, "Variables" | "Coordinates"] := coordinates

Prop[MetricTensor[_, _, indices_] ? MetricTensorQ, "Indices"] := indices


Prop[_, "Properties"] := MetricTensor["Properties"]

Prop[mt_, "Dimension" | "Dimensions"] := Length[mt["Coordinates"]]

Prop[mt_, "MatrixRepresentation"] :=
    Switch[mt["Indices"],
        {True, True}, mt["Matrix"],
        {False, False}, Inverse[mt["Matrix"]],
        _, IdentityMatrix[mt["Dimension"]]
    ]

Prop[mt_, "Signature"] := Block[{
    eigenvalues = Eigenvalues[mt["MatrixRepresentation"]]
},
    {Count[eigenvalues, _ ? Positive], Count[eigenvalues, _ ? Negative], Count[eigenvalues, EqualTo[0]]}
]

Prop[mt_, "FullSignature"] := With[{signature = mt["Signature"]},
    Append[signature, mt["Dimension"] - Total[signature]]
]

Prop[mt_, "SignatureVector"] := Block[{
    p, q, r
},
    {p, q, r} = mt["Signature"];
    Join[
        ConstantArray[1,  p],
        ConstantArray[- 1, q],
        ConstantArray[0, r]
    ]
]

Prop[mt_, "Type"] := Switch[
    mt["Indices"]
    ,
    {True, True},
    "Covariant"
    ,
    {False, False},
    "Contravariant"
    ,
    _,
    "Mixed"
]

Prop[mt_, "SignatyreType"] := Switch[
    mt["Signature"],
    {0, 0, 0}, "Unknown",
    {p_, 0, p_} | {0, q_, q_}, "Riemannian",
    {p_, q_, 0}, "Pseudo-Riemannian",
    {1, _, 0}, "Lorentzian",
    {_, _, 0}, "Pseudo-Riemannian",
    _, "General"
]

Prop[mt_, "Symmetry"] := TensorSymmetry[mt["Tensor"]]

Prop[mt_, "Symbol"] := Switch[
    mt["Type"]
    ,
    "Covariant", Subscript[g, Row[{mu, nu}]]
    ,
    "Contravariant", Superscript[g, Row[{mu, nu}]]
    ,
    "Mixed", Subsuperscript[g, mu, nu]
]

Prop[mt_, "Inverse" | "InverseMetricTensor"] := MetricTensor[mt, False, False]


(* Formatting *)

MetricTensor /: MakeBoxes[mt_MetricTensor /; MetricTensorQ[Unevaluated[mt]], TraditionalForm] := With[{
    boxes = ToBoxes[Normal[mt["MatrixRepresentation"]], TraditionalForm]
},
    InterpretationBox[
        boxes,
        mt
    ]
]
    

MetricTensor /: MakeBoxes[mt_MetricTensor /; MetricTensorQ[Unevaluated[mt]], form_] := Block[{
    m = mt["Matrix"], icon
},
    icon = MatrixPlot[
        Map[Replace[{x_ ? (Not @* NumericQ) :> BlockRandom[RandomComplex[], RandomSeeding -> Hash[x]], x_ :> N[x]}], m, {2}],
        ImageSize -> Dynamic[{Automatic, 3.5 * (CurrentValue["FontCapHeight"] / AbsoluteCurrentValue[Magnification])}],
        Frame -> False, FrameTicks -> None
    ];

    BoxForm`ArrangeSummaryBox["MetricTensor", mt, icon,
        {
            {
                BoxForm`SummaryItem[{"Type: ", mt["Type"]}],
                BoxForm`SummaryItem[{"Symbol: ", mt["Symbol"]}]
            },
            {
                BoxForm`SummaryItem[{"Dimensions: ", mt["Dimensions"]}], 
                BoxForm`SummaryItem[{"Coordinates: ", mt["Coordinates"]}]   
            }
        },
        {
            {
                BoxForm`SummaryItem[{"Signature: ", mt["SignatyreType"]}],
                BoxForm`SummaryItem[{"Symmetry: ", mt["Symmetry"]}]
            }
        },
        form,
        "Interpretable" -> Automatic
    ]
]

