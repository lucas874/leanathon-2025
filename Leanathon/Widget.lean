import Lean
import ProofWidgets.Component.GraphDisplay
import ProofWidgets.Component.HtmlDisplay
open Lean Widget
open ProofWidgets Jsx

@[widget_module]
def helloWidget : Widget.Module where
  javascript := "
    import { Graphviz } from 'https://esm.sh/graphviz-react'
    import * as React from 'react'
    export default function(props) {
      const name = props.name || 'world';
      return React.createElement('div', {}, `Hello ${name}!`)
    }
  "

#widget helloWidget

structure HelloWidgetProps where
  name? : Option String := none
deriving Server.RpcEncodable

#widget helloWidget with {name? := "DTU" : HelloWidgetProps }






def mkEdge (st : String × String) : GraphDisplay.Edge := {
  source:=st.1,
  target:=st.2,
  label?:=<g><text textAnchor="middle" dominantBaseline="middle">Edge</text></g>
}

#html <GraphDisplay
  vertices={#["a", "b", "c"].map ({id:=·})}
  edges={#[("a","b")].map mkEdge}
  forces={#[
    .link {distance? := some 100}
  ]}
/>
