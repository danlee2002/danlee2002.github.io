---
layout: page
title: Software Foundations Day 1
---

<h1>  Introduction</h1>
In this blog, I shall began documenting my progress through <a href = "https://www.seas.upenn.edu/~cis5000/current/index.html">UPenn's CIS: Software Foundations Course</a>, a course dedicated on the mathematical underpinning of what makes up reliable software. Before we begin we need to first set up coq, the language we will be using to verify software. 
The easiest way to install COQ is to install via opam, ocaml's package manager. For the linux operating system we can simply run the following command: 

```bash
bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
```
For mac users, we can set up this via hombrew:
```bash
brew install opam
```
Moreover, for mac users one needs to ensure they have gnu patch installed so if one doesn't already have gpatch run the following command:
```bash
brew install gpatch
```
We can now verify if opam installed properly using the following command `opam --version`.
To finalize our setup we need to setup coq and our ide. To do this, let's first initialize an opam switch `opam switch create coq [ocaml version]`. 
With our switch initalized we can now install coq needed `opam install coq` and verify installation via `coqc --version`. 
The final step is to choose an ide of one's choice, there are many different options such as Coqtail, Proof General, and vscoq for my use case I shall be personally using <a  href = "https://github.com/coq-community/vscoq">vscoq</a>.
<h1> Getting Started </h1>
With our initial setup out of the way, we can begin looking into the basic syntax of coq:
<h3>Inductive Types</h3> 
In coq, we can define inductive types utilizing a set of constructors in the following notation. In this case, `value1,value2,value3` are all constructors: 
```coq
Inductive typename: Type:=
|value1
|value2
|value3.
```
Now in a similar fashion we can also define functions on a type via the `Definition` keyword:
```coq
Definition funcname (input:type): returnType :=
    match input with
    |val1 => output1
    |val2 => output2.

```
In this snippet, the `match` keyword can be thought of as a case statement in traditional programming languages and we enumerate each case via the notation `|val1` and specify the return value via arrow notation `=>`.   \
To call a function we use the `Computer operator`:
```coq
Compute (func val).
    
```
As a more concrete sample here is a following implementation of a boolean class:
```coq
Inductive bool: Type:=
|true
|false.

Definition negb(b1: bool): bool :=
	match b1 with 
	|true => false
	|false =>  true
	end.
Definition andb(b1: bool) (b2: bool): bool := 
	match b1 with
		| true => b2
		| false => false
	end.
Definition orb(b1: bool) (b2: bool): bool := 
	match b1 with
		| true => true
		| false => b2
	end.
(**we can perform operations on the function above using the following notation**)
Compute (orb false false).
(**we can also simplify notation with the notation construct**)
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
```
In software, it is very important to verify if one's software creates the intended outcome. For coq, we can perform this via assertions and proofs using the following notation:
```coq
(**stores assertion, call "Example" keyword to perform assertion and equality operator = to compare to desire value**)
Example test_orb5:  false || false || true = true.
(**performs reflexive proof to ensure values are intended**)
Proof. simpl. reflexivity. Qed.
```
Moreover like many programming languages there exists conditional statments, however the way they work is a bit different since boolean dont exist by default. In coq, the first value within a defined inductive type is the value that evaluates to true:
```coq
(**consider the following snippet of code**)
Inductive bool: Type :=
    |true
    |false.

Definition val(b1: bool): type  :=
    if b1 then true else false.
(**return true**)
Computer (val true).
(**return false**)
Computer (val false).
```
Moreover, in a similar manner to python's `type()` function we can check for types using the `Check` function.
```
Check true.
(**the following snippet of code can be thought of as performing type assertion**)
Check true
  : bool.
Check (negb true)
  : bool.

(** since functions are also types we can also check for types. in this scenario we are basically checking to see if input of function is of the correct set and maps to appropriate output**)
Check negb:
    bool -> bool.
```
In traditional programming languages, we often have constructs for polymorphism. In a similar manner, we can derive other inductive types from existing inductive type. The previous types that we encountered are what we call enumerated types as they consist of a finite set of elements called constrictors. Let's look at more nuanced type:
```coq
(**enumerated type**)
Inductive rgb: Type :=
    |red 
    |green 
    |blue.
(**deriving from rgb**)
Inductive color: Type :=
    |black 
    |white 
    |primary (p: rgb).
```
The following snippet of code or inductive performs two functions: 
<ol>
    <li> Create a new set of constructors i.e red, green, blue. </li>
    <li> Bundle them under a new named type rgb in our case. </li>

</ol>
In the case of primary we are basically defining a color value that takes in a constructor of the named type rgb and use to define a new constructor called primary that belong in [rgb] and [color].
<h3>Basics Solution</h3>
With some basics out of the way we can begin hacking away at the problem set following this course. The link can be found <a href ="https://www.seas.upenn.edu/~cis5000/current/index.html">here</a>.
<h4>Exercise 1:</h4>
<b>nandb</b>
```coq
(** **** Exercise: 1 star, standard (nandb)

    The [Admitted] command can be used as a placeholder for an
    incomplete proof.  We use it in exercises to indicate the parts
    that we're leaving for you -- i.e., your job is to replace
    [Admitted]s with real proofs.

    Remove "[Admitted.]" and complete the definition of the following
    function; then make sure that the [Example] assertions below can
    each be verified by Coq.  (I.e., fill in each proof, following the
    model of the [orb] tests above, and make sure Coq accepts it.) The
    function should return [true] if either or both of its inputs are
    [false].

    Hint: if [simpl] will not simplify the goal in your proof, it's
    probably because you defined [nandb] without using a [match]
    expression. Try a different definition of [nandb], or just
    skip over [simpl] and go directly to [reflexivity]. We'll
    explain this phenomenon later in the chapter. **)

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  |true => if b2 then false else true
  |false => true 
  end.

Example test_nandb1:               (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2:               (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3:               (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4:               (nandb true true) = false.
Proof. simpl. reflexivity. Qed.
(** [] *)
```
<b>andb3</b>
```coq
(** **** Exercise: 1 star, standard (andb3)

    Do the same for the [andb3] function below. This function should
    return [true] when all of its inputs are [true], and [false]
    otherwise. *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool:=
  match b1 with
    |false => false
    |true => match b2 with 
            |false => false
            |true => b3
            end
    end.


Example test_andb31:                 (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32:                 (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33:                 (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34:                 (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(** [] *)
```
