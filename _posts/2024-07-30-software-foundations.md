---
layout: page
title: Software Foundations Day 1
---

<h1>  Introduction</h1>
In this blog, I shall began documenting my progress through <a href = "https://www.seas.upenn.edu/~cis5000/current/index.html">UPenn's CIS: Software Foundations Course</a>, a course dedicated on providing introduction to the mathematical underpinning of what makes up reliable software. Before we begin we need to first set up COQ, the language we will be using to verify software. The easiest way to install COQ is to install via opam, ocaml's package manager. For the linux operating system we can simply run the following command: 

```bash
bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
```
For mac users, we can set up this via hombrew:
```bash
brew install opam
```
Moreover, for mac users in order to utilize COQ one needs to ensure they have gnu patch installed so if one doesn't already have gpatch installed also run the following command:
```bash
brew install gpatch
```
Once installation finishes we can verify if opam installed properly using the following command `opam --version`.
Now to finalize our setup we need to setup coq and our ide. To do this, let's first initialize an opam switch `opam switch create coq [ocaml version]`. 
With our switch initalized we can now install COQ as needed `opam install coq` and verify installation via `coqc --version`. 
The final step is to choose an ide of one's choice, there are many different options such as Coqtail, Proof General, and vscoq for my use case I shall be personally using <a  href = "https://github.com/coq-community/vscoq">vscoq</a>.
<h1> Getting Started </h1>
With our initial setup out of the way, we can begin looking into the basic structures of Coq:
<h3>Inductive Types</h3> 
In coq, we can define inductive types utilizing the following notation: 
```coq
Inductive typename: Type:=
|value1
|value2
|value3.
```
Now in a similar fashion we can also define functions on a type via the following syntax:
```coq
Definition (val1:type): type :=
    match val1 with
    |val1 => output1
    |val2 => output2.

```
To call a function we use the `Computer operator`:
```coq
Compute (func val).
    
```
As a more concrete sample here is a following definition of a boolean class:
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
We can also perform assertions and proves using the following notation:
```coq
Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.
```
<h3>Basics Solution</h3>
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
    explain this phenomenon later in the chapter. *)

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

