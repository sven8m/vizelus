To compile this version of Zelus with visualization : 
We need the interLib, kgraph, kdata and kplacement librairies installed with dune.
After that, it can be compiled locally with 
```make install``` or ```make reinstall``` (in the parent directory).

The use is then as with Zelus.
Use ```zeluc --help``` to see the options.
`-viz` is for the first visualization.
`-viz2` designates the filtered approach.

`zeluc -viz <file>.zls` produces a <file>.kgx file which can be opened in VS code on Kieler Eclipse.

