# boolean-simplifier

A stupid worse-is-better library for simplifying Boolean expressions. Example:

```clojure
(require '[boolean-simplifier.core :as bs])
(bs/simplify '[:and int? [:and int? pos?]])
;; => [:and int? pos?]
```

The input language:

* `true` and `false` are literals
* `[:and ...]` is a conjunction
* `[:or ...]` is a disjunction
* `[:not ...]` is a negation
* Any other values are variables.

It is based on the following rules:

* When evaluating `b` in `[:and a b]`, we know that `a` is true.
* When evaluating `b` in `[:or a b]`, we know that `a` is false.
* `[:not [:not x]]` is equivalent to `x`

The library does *not* use the distributive law. Example:

```clojure
(bs/simplify '[:or [:and int? pos?] [:and int? neg?]])
;; => [:or [:and int? pos?] [:and int? neg?]]
;; Ideally the result would be [:and int? [:or pos? neg?]]
```

## Usage

Not released; use [a git dependency with deps.edn](https://clojure.org/guides/deps_and_cli#_using_git_libraries):

```clojure
{:deps
  {miikka/boolean-simplifier
    {:git/url "https://github.com/miikka/boolean-simplifier"
     :sha     "INSERT SHA HERE"}}}
```

## See also

* [Quine-McCluskey algorithm](https://en.wikipedia.org/wiki/Quine–McCluskey_algorithm) would be the "proper" solution
* [Reduced Ordered Binary Decision Diagram (ROBDD)](https://en.wikipedia.org/wiki/Binary_decision_diagram) seems useful as well

## License

Copyright 2019 Miikka Koskinen.

This program and the accompanying materials are made available under the
terms of the Eclipse Public License 2.0 which is available at
http://www.eclipse.org/legal/epl-2.0.

This Source Code may also be made available under the following Secondary
Licenses when the conditions for such availability set forth in the Eclipse
Public License, v. 2.0 are satisfied: GNU General Public License as published by
the Free Software Foundation, either version 2 of the License, or (at your
option) any later version, with the GNU Classpath Exception which is available
at https://www.gnu.org/software/classpath/license.html.
