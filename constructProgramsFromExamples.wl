(* ::Package:: *)

(* ::Text:: *)
(*Definitions of functions performing list transformations:*)


identity[list_, example_] := {{Identity}, {Identity[list]}}


(* ::Text:: *)
(*Functions which change the order of elements in lists:*)


sort[list_, example_] := {{Sort}, {Sort[list]}}


reverseSort[list_, example_] := {{ReverseSort}, {ReverseSort[list]}}


reverse[list_, example_] := {{Reverse}, {Reverse[list]}}


rotateRight[list_, example_, range_: - 1] := Module[{r},
	If[range == -1, r = Range[Length[list] - 1], r = range];
	{Map[Function[shift, RotateRight[#, shift]&], r], Map[RotateRight[list, #]&, r]}
]


(* ::Text:: *)
(*Functions adding elements to lists:*)


joinOld[list_, example_] := Module[{input, output, func},
	input = example[[1]];
	output = example[[2]];
	func = output /. {pre___, Sequence @@ input, post___} :> Which[
		Length[List[pre]] == 0 && Length[List[post]] == 0, Join[#]&,
		Length[List[pre]] == 0, Join[#, List[post]]&,
		Length[List[post]] == 0, Join[List[pre], #]&,
		True, Join[List[pre], #, List[post]]&
		];
	{func, func[list]}
]


join[list_, example_] := Module[{input, output, positions, additions, funcs},
	input = example[[1]];
	output = example[[2]];
	positions = SequencePosition[output, input];
	additions = Map[{output[[ ;; #[[1]] - 1]], output[[#[[2]] + 1 ;; ]]}&, positions];
	funcs = Function[lists, 
				With[{pre = lists[[1]], post = lists[[2]]},
					Which[
						Length[pre] == 0 && Length[post] == 0, Join[#]&,
						Length[pre] == 0, Join[#, post]&,
						Length[post] == 0, Join[pre, #]&,
						True, Join[pre, #, post]&
					]
				] 
			] /@ additions;
	{funcs, Map[Function[func, func[list]], funcs]}
]	


(* ::Text:: *)
(*The recent (best) implementation of Join function:*)


joinNew[list_, example_] := Module[{input, output, rules, func},
	input = example[[1]];
	output = example[[2]];
	rules = { 
		{s__, Sequence @@ input} :> With[{l = List[s]}, (Join[l, #]&)], 
		{Sequence @@ input, s__} :> With[{l = List[s]}, (Join[#, l]&)], 
		{s1__, Sequence @@ input, s2__} :> With[{l1 = List[s1], l2 = List[s2]}, (Join[l1, #, l2]&)]
		};
	func = output /. rules;
	If[func === output, {{}, {}}, {{func}, {func[list]}}]
]	


riffle[list_, example_] := Module[
	{input, output, elems, positions, funcs, pre, introducedElem, post, elemPoss, elemStep},
	input = example[[1]];
	output = example[[2]];
	elems = output /. {
		pre___?(MatchQ[input, {___, #, ___}]&),
		PatternSequence[elem_, ___?(MatchQ[input, {___, #, ___}]&)]..,
		post___?(MatchQ[input, {___, #, ___}]&)
		} :> {List[pre], elem, List[post]};
	If[elems === output,
		positions = Sort[Flatten[Map[Position[output, #]&, Union[input]]]];
		If[positions === Range[1, Length[output] - 1, 2], 
			funcs = With[{l = output[[2 ;; Length[output] ;; 2]]}, {Riffle[#, l]&}],
			funcs = {}
		],
		
		{pre, introducedElem, post} = elems;
		elemPoss = Flatten[Position[output, introducedElem]];
		elemStep = Union[MapThread[(#2 - #1)&, {elemPoss[[ ;; -2]], elemPoss[[2 ;; ]]}]];
		If[Length[elemStep] == 1, 
			funcs = With[
				{x = introducedElem, i = elemPoss[[1]], j = elemPoss[[-1]], s = elemStep[[1]]}, 
				{Riffle[#, x, {i, j, s}]&}
				],
			funcs = {}
		]
	];
	{funcs, Map[Function[func, func[list]], funcs]}
]


(* ::Text:: *)
(*Functions extracting parts of lists:*)


arange[formList_, lattList_] := Module[{formListCut, lattListCut},
	lattListCut = Select[lattList, # > Min[formList]&];
	formListCut = Select[formList, # < Max[lattList]&];
	Sow[formListCut];
	lattListCut
]


posToPartFunctions[positionList_] := Which[
	Length[positionList] == 1 && Length[First[positionList]] == 1, 
		With[{pos = positionList[[1]]}, #[[pos]]& ],
	Length[positionList] == 1, 
		With[{pos1 = positionList[[1]][[1]], pos2 = positionList[[1]][[-1]]}, #[[pos1 ;; pos2]]& ],
	(Length[Union[Length /@ positionList]] == 1 && 
		Length[Union[MapThread[#2[[1]] - #1[[-1]]&, {positionList[[;;-2]], positionList[[2;;]]}]]] == 1),
			With[{pos1 = positionList[[1]][[1]], pos2 = positionList[[-1]][[-1]], step = positionList[[2]][[1]] - positionList[[1]][[-1]]},
				#[[pos1 ;; pos2 ;; step]]& ],
	True, With[{posVec = Flatten[positionList]}, #[[posVec]]& ]
	]


part[list_, example_] := Module[{input, output, positions, tidied, array, gathered, funcs},
	input = example[[1]];
	output = example[[2]];
	positions = Map[Flatten[Position[input, #]]&, output];
	tidied = Reap[Fold[arange, positions]];
	tidied = Join[If[Length[tidied[[2]]] == 0, {}, tidied[[2]][[1]]], {tidied[[1]]}];
	array = Array[
		MapIndexed[Function[{elem, index}, tidied[[index[[1]]]][[elem]]], List[##]]&, 
		Map[Length, tidied]
		];
	array = Select[
		Partition[Flatten[array], Length[tidied]], 
		OrderedQ[#, Less]&
		];
	gathered = Map[Function[l, Split[l, (#1 + 1 == #2)&]], array];
	funcs = Map[posToPartFunctions, gathered];
	{funcs, Map[Function[func, func[list]], funcs]}
]


posToDropFunctions[positionList_] := Which[
	Length[positionList] == 1 && Length[First[positionList]] == 1, 
		With[{pos = positionList[[1]]}, Drop[#, pos]& ],
	Length[positionList] == 1, 
		With[{pos = positionList[[1]]}, Drop[#, pos]& ],
	(Length[Union[Length /@ positionList]] == 1 && 
		Length[Union[MapThread[#2[[1]] - #1[[-1]]&, {positionList[[;;-2]], positionList[[2;;]]}]]] == 1),
			With[{pos1 = positionList[[1]][[1]], pos2 = positionList[[-1]][[-1]], step = positionList[[2]][[1]] - positionList[[1]][[-1]]},
				Drop[#, {pos1, pos2, step}]& ],
	True, {}
	]


drop[list_, example_] := Module[
	{input, output, positions, tidied, array, gathered, positionsRev, gatheredRev, funcs},
	input = example[[1]];
	output = example[[2]];
	positions = Map[Flatten[Position[input, #]]&, output];
	tidied = Reap[Fold[arange, positions]];
	tidied = Join[If[Length[tidied[[2]]] == 0, {}, tidied[[2]][[1]]], {tidied[[1]]}];
	array = Array[
		MapIndexed[Function[{elem, index}, tidied[[index[[1]]]][[elem]]], List[##]]&, 
		Map[Length, tidied]
		];
	array = Select[
		Partition[Flatten[array], Length[tidied]], 
		OrderedQ[#, Less]&
		];
	gathered = Map[Function[l, Split[l, (#1 + 1 == #2)&]], array];
	positionsRev = Map[Complement[Range[Length[input]], ##]& @@ # &, gathered];
	gatheredRev = Map[Function[l, Split[l, (#1 + 1 == #2)&]], positionsRev];
	gatheredRev = Replace[gatheredRev, {first_, __, last_} :> {first, last}, -1];
	funcs = Map[posToDropFunctions, gatheredRev];
	{funcs, Map[Function[func, func[list]], funcs]}
]


union[list_, example_] := {{Union}, {Union[list]}}


(* ::Text:: *)
(*Functions applied to elements of lists:*)


findFormula[list_, example_] := Module[{formula},
	formula = FindFormula[Transpose[example]];
	{{formula}, {formula[list]}}
]


(* ::Text:: *)
(*Rules transforming more generic functions into more specific ones:*)


rotateFunctionRule = Function[RotateRight[_, n_]] :> {	
	RotateRight[#, n]&,
	RotateLeft[#, -n]&,
	RotateLeft[#, Length[#] - Mod[n, Length[#]]]&,
	RotateRight[#, -(Length[#] - Mod[n, Length[#]])]&
	};


joinFunctionRule = {
	Function[Join[Slot[_], elem_]] :> With[{el = First[elem]}, (Append[#, el]&)] /; Length[elem] == 1,
	Function[Join[elem_, Slot[_]]] :> With[{el = First[elem]}, (Prepend[#, el]&)] /; Length[elem] == 1,
	Function[Join[Slot[_], elem_]] :> With[{
		pattern = elem /. {PatternSequence[patt__]..} :> List[patt],
		elemLen = Length[elem]
		},
		If[Length[pattern] < elemLen, 
			If[Length[pattern] > 1, 
				(PadRight[#, Length[#] + elemLen, pattern]&), 
				(PadRight[#, Length[#] + elemLen, First[pattern]]&)
			],
			(Join[#, elem]&)
		]
	],
	Function[Join[elem_, Slot[_]]] :> With[{
		pattern = elem /. {PatternSequence[patt__]..} :> List[patt],
		elemLen = Length[elem]
		},
		If[Length[pattern] < elemLen, 
			If[Length[pattern] > 1, 
				(PadLeft[#, Length[#] + elemLen, pattern]&), 
				(PadLeft[#, Length[#] + elemLen, First[pattern]]&)
			],
			(Join[elem, #]&)
		]
	],
	Function[Join[elemL_, Slot[_], elemR_]] :> With[{
		patternL = elemL /. {PatternSequence[patt__]..} :> List[patt],
		patternR = elemR /. {PatternSequence[patt__]..} :> List[patt],
		elemLLen = Length[elemL],
		elemRLen = Length[elemR]
		},
		If[patternL === patternR && (Length[patternL] < elemLLen || Length[patternL] < elemRLen), 
			If[Length[patternL] > 1, 
				(PadRight[#, Length[#] + elemLLen + elemRLen, patternL, elemLLen]&), 
				(PadRight[#, Length[#] + elemLLen + elemRLen, First[patternL], elemLLen]&)
			],
			(Join[elemL, #, elemR]&)
		]
	]
};


padRightFunctionRule = Function[PadRight[Slot[_], nTotal_, patt_, nLeft___]] :> {
	PadRight[#, nTotal, patt, nLeft]&,
	PadLeft[#, -nTotal, patt, nLeft]&
	};


padLeftFunctionRule = Function[PadLeft[Slot[_], nTotal_, patt_, nLeft___]] :> {
	PadLeft[#, nTotal, patt, nLeft]&,
	PadRight[#, -nTotal, patt, nLeft]&
	};


riffleFunctionRuleF[example_] := {
	Function[Riffle[Slot[_], x_, {i_, j_, s_}]] :> {Riffle[#, x, {i, j, s}]&, Riffle[#, x]&, Riffle[#, x, s]&} /; 
		(i == 2 && j == Length[example[[2]]] - 1 && s == 2),
	Function[Riffle[Slot[_], x_, {i_, j_, s_}]] :> {Riffle[#, x, {i, j, s}]&, Riffle[#, x, s]&} /; 
		(i == s && j == Length[example[[2]]] - s + 1)
	}


partFunctionRuleF[example_] := {
	Function[Part[Slot[_], l_?ListQ]] :> 
		With[{ind = l[[1]], n = Length[example[[1]]] - 1}, {#[[ind]]&, First, Take[#, 1]&, Drop[#, -n]&}] /; 
			(Length[l] == 1 && l[[1]] == 1),
	Function[Part[Slot[_], l_?ListQ]] :> 
		With[{ind = l[[1]], n = Length[example[[1]]] - 1}, {#[[ind]]&, #[[-1]]&, Last, Take[#, -1]&, Drop[#, n]&}] /; 
			(Length[l] == 1 && l[[1]] == Length[example[[1]]]),
	Function[Part[Slot[_], l_?ListQ]] :> With[{ind = l[[1]]}, #[[ind]]&] /; Length[l] == 1,
	Function[Part[Slot[_], Span[i_, j_]]] :> 
		{#[[ ;; j]]&, #[[ ;; -2]]&, Take[#, j]&, Most, Drop[#, -1]&} /; (i == 1 && j + 1 == Length[example[[1]]]),
	Function[Part[Slot[_], Span[i_, j_]]] :> 
		With[{ind1 = Length[example[[1]]] - j + 1, ind2 = j + 1}, 
			{#[[ ;; j]]&, #[[ ;; -ind1]]&, Take[#, j]&, Drop[#, ind2]&}
		] /; i == 1,
	Function[Part[Slot[_], Span[i_, j_]]] :> 
		With[{ind = j - 1}, {#[[i ;; ]]&, Take[#, -ind]&, Rest, Drop[#, 1]&}] /; (i == 2 && j == Length[example[[1]]]),
	Function[Part[Slot[_], Span[i_, j_]]] :> 
		With[{ind1 = j - i + 1, ind2 = i - 1}, 
			{#[[i ;; ]]&, #[[-ind1 ;; ]]&, Take[#, -ind1]&, Drop[#, ind2]&}
		] /; j == Length[example[[1]]],
	Function[Part[Slot[_], Span[i_, j_]]] :> {#[[i ;; j]]&, Take[#, {i, j}]&}
	}


dropFunctionRuleF[example_] := {
	Function[Drop[Slot[_], {i_, j_}]] :> (Drop[#, j]&) /; i == 1,
	Function[Drop[Slot[_], {i_, j_}]] :> With[{n = (j - i + 1)}, Drop[#, -n]&] /; j == Length[example[[1]]]
	}


(* ::Text:: *)
(*Entropy functions:*)


(* ::Text:: *)
(*A faster one:*)


entropy[examples_] := -N[
	Total[
		Map[# Log2[#]&, 
			Map[Last, Tally[examples]] / Length[examples]
		]
	]
]


(* ::Text:: *)
(*A slightly slower one:*)


entropy2[examples_] := Module[{p},
	p = Map[Last, Tally[examples]] / Length[examples];
	-N[Total[p * Log2[p]]]
]


(* ::Text:: *)
(*A function generating a list of random input lists:*)


generateExamples[examplesN_, exampleShape_] := Union[
	RandomInteger[Times @@ exampleShape, Prepend[exampleShape, examplesN]]
]


(* ::Text:: *)
(*A function applying list of functions to an example of a pair of lists:*)


runFunctions[funcList_, example_, inputExample_] := Through[funcList[example, inputExample]]


(* ::Text:: *)
(*Generating additional questions about the input:*)


generateQuestion[example_] := Module[{questionText, ans},
	questionText = StringTemplate[
		"Given `1`, what would be the output generated by the desired function?"
		][example];
	ans = Ask["x"  -> <|"Interpreter" -> (DelimitedSequence["Number", {"{", ",", "}"}] | "Number"), "Label" :> questionText|>];
	If[Head[ans] === List, ans, List[ans]]
]


(* ::Text:: *)
(*Checking the first example given by the user:*)


tryInput[funcList_, example_, dims_] := Module[
	{res, funcs, funcMultiplicity, funcIndices, indexDict, outputs, pos, narrowedFuncList},
	res = runFunctions[funcList, example[[1]], example];
	funcs = res[[All, 1]];
	funcMultiplicity = Map[Length, funcs];
	funcIndices = Flatten[Map[ConstantArray[#, funcMultiplicity[[#]]]&, Range[Length @ funcMultiplicity]]];
	indexDict = AssociationThread[Range[Length[funcIndices]], funcIndices];
	funcs = Flatten[funcs];
	outputs = Flatten[res[[All, -1]], 1];
	pos = Flatten[Position[outputs, _?(# === example[[2]] || # == example[[2]] &)]];
	If[Length[pos] == 0, narrowedFuncList = {},
		If[Length[pos] == 1, 
			narrowedFuncList = funcs[[pos]], 
			narrowedFuncList = funcList[[indexDict[#]& /@ pos]]
		]
	];
	{narrowedFuncList, example, dims}
]


(* ::Text:: *)
(*Checking further examples:*)


narrowDown[{funcList_, example_, dims_}] := Module[
	{exampleList, res, funcs, funcMultiplicity, funcIndices, indexDict, outputs, s, maxPos, selExample, 
		answer, outputPos, matchingTemplateFuncs, narrowedFuncList,
		conversionRules = {drop -> part}},
	exampleList = generateExamples[10, dims];
	res = Map[runFunctions[funcList, #, example]&, exampleList];
	funcs = First[res[[All, All, 1]]];
	funcMultiplicity = Map[Length, funcs];
	funcIndices = Flatten[Map[ConstantArray[#, funcMultiplicity[[#]]]&, Range[Length @ funcMultiplicity]]];
	indexDict = AssociationThread[Range[Length[funcIndices]], funcIndices];
	funcs = Flatten[funcs];
	outputs = Map[Flatten[#, 1]&, res[[All, All, -1]]];
	s = entropy /@ outputs;
	maxPos = FirstPosition[s, Max[s]][[1]];
	selExample = exampleList[[maxPos]];
	answer = generateQuestion[selExample];
	outputPos = Flatten[Position[outputs[[maxPos]], _?(# === answer || # == answer &)]];
	If[Length[outputPos] == 0, narrowedFuncList = {},
		matchingTemplateFuncs = funcList[[indexDict[#]& /@ outputPos]];
		Which[
			Length[outputPos] == 1, narrowedFuncList = funcs[[outputPos]],
			SameQ[##]& @@ (matchingTemplateFuncs /. conversionRules), narrowedFuncList = funcs[[outputPos]][[{1}]],
			True, narrowedFuncList = funcList[[indexDict[#]& /@ outputPos]]
		];
	];
	{narrowedFuncList, example, dims}
]


(* ::Text:: *)
(*Main loop:*)


findFunction[funcList_, example_, dims_: {4}] := NestWhile[
		narrowDown, 
		tryInput[funcList, example, dims], 
		Length[First[#, {}]] > 1&
	]


(* ::Text:: *)
(*Selecting a list of valid functions based on the first input:*)


checkInput[exampleInput_] := Module[{dict, example, lenExampleIn, lenExampleOut},
	dict = <|
		"orderChangingFunctions" -> {identity, sort, reverseSort, reverse, rotateRight},
		"lengthIncreasingFunctions" -> {join, riffle},
		"lengthReducingFunctions" -> {part, drop, union},
		"elementChangingFunctions" -> {findFormula}
		|>;
	
	SeedRandom[Hash[{Ask["input"], Ask["output"], $RequesterAddress}]];	
	(*The seed is needed for cloud-deployment. The reason is that in the cloud values of 
	variables are not being stored. Every time an input is sent the whole thing gets reexecuted*)
	
	example = {
		exampleInput[[1]],
		If[Head[exampleInput[[2]]] === List, exampleInput[[2]], List[exampleInput[[2]]]]
		};
	lenExampleIn = Length[example[[1]]];
	lenExampleOut = Length[example[[2]]];
	Which[
		(lenExampleIn == lenExampleOut) && Sort[example[[1]]] == Sort[example[[2]]], 
			findFunction[dict["orderChangingFunctions"], example],
		(lenExampleIn == lenExampleOut) && (And @@ Map[NumberQ, example[[1]]]) && (And @@ Map[NumberQ, example[[2]]]),
			findFunction[dict["elementChangingFunctions"], example],
		(Length[example[[1]]] < Length[example[[2]]]) && (And @@ Map[Count[example[[1]], #] == Count[example[[2]], #]&, Union[example[[1]]]]),
			findFunction[dict["lengthIncreasingFunctions"], example, {Length[example[[1]]]}],
		(Length[example[[1]]] > Length[example[[2]]]) && (And @@ Map[Count[example[[1]], #] == Count[example[[2]], #]&, Union[example[[2]]]]),
			findFunction[dict["lengthReducingFunctions"], example, {Length[example[[1]]]}],
		True, {{}, {}, {}}
	]
]


(* ::Text:: *)
(*Applying function-transforming rules to the functions selected as performing the desired transformation:*)


generalize[func_, example_, dims_] := Module[{f, shift, i, shifts, funcList, ex, d},
	If[Length[func] == 0, Return[$Failed], f = func[[1]]];
	If[MatchQ[f, Function[RotateRight[_, _]]],
		shift = f /. Function[RotateRight[_, s_]] :> s;
		If[shift < Length[example], 
			i = Quotient[Length[example] - 1 - shift, dims[[1]]];
			shifts = Table[dims[[1]] x + shift, {x, 0, i}];
			{funcList, ex, d} = narrowDown[{{rotateRight[#, shifts]&}, example, {Length[example[[1]]]}}];
			f = funcList[[1]];
		]
	];
	f = f /. 
		{rotateFunctionRule, Sequence @@ joinFunctionRule, Sequence @@ partFunctionRuleF[example], 
		Sequence @@ dropFunctionRuleF[example], Sequence @@ riffleFunctionRuleF[example]};
	f = f /. {padRightFunctionRule, padLeftFunctionRule};
	If[Head[f] === List, Column[f], f]
]


(* ::Text:: *)
(*Embedding everything in AskFunction:*)


ask = AskFunction[
		Replace[generalize @@ checkInput[{
			Ask[{"input", "Please enter input list."} ->
				DelimitedSequence["Number" | "String", {"{", ",", "}"}]
			],
			Ask[{"output", "Please enter output list."} -> 
				(DelimitedSequence["Number" | "String", {"{", ",", "}"}] | "Number" | "String")
			]
		}], $Failed -> "Sorry, could not find a function."]
	];


(* ::Text:: *)
(*Cloud-deploying:*)


CloudDeploy[ask,"functionFinder",Permissions->"Public"]
