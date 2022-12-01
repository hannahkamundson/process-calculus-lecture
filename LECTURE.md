# Process Calculus - Milner Versions

## Intro
The idea of both Calculus of Communicating Systems and $\pi$-Calculus is the interaction between systems mathematically models systems that communicate with each other. Milner's models label both the system components and the channels that communicate between them. 

We will explore non-value passing CCS and untyped $\pi$-Calculus. $\pi$-Calculus builds off of the concepts of CCS, so we will start there.

## Calculus of Communicating Systems (CCS)

CCS was developed when Milner attempted to apply sequential semantic ideas to a concurrent programming language. The sequential semantic ideas assumed that the program being analyzed had sole control over the memory, which he found particularly problematic on concurrent programs where a program's memory may be modified by other programs. Thus, CCS was born. CCS is Turing Complete.

We are first going to focus on a calculus that does not pass values betweeen agents.

### Syntax
Recall from previous lectures we have defined
```
var := string
```

We now need syntax to describe the ports going in and out of an agent. The "in" ports are just any string, and the "out" ports are one of the "in" ports with a bar over it.
```*
in := var
out := Bar in
```

Thus, any port has a "label", defined as
```
label := in 
    | out
```

Additionally, there are a set of "actions" that can be taken by a given agent. For example, one agent can send data out of a channel and another agent can recieve data in a channel. There are also internal or silent actions. These are actions that happen within an agent for which we don't have labels. We will call this $\tau$. We can define this formally as such
```
action := label
    | τ
```

We are now ready to define our process expressions (also called agent expressions) for CCS.
```
expr := skip
    | var <- expr
    | action.expr
    | expr + expr
    | expr | expr
    | expr\label
    | expr[label:label]
```

Let's break out what these different expressions mean.

1. **Skip** - $skip$: As it was in prior classes, the first expression simply means the program has terminated and we should "do nothing".

2. **Constant** - $var \gets expr$: The second expression stores a process expression ($expr$) as an agent ($var$). This means agents can be defined in terms of each other. This is confusingly called a "constant" in the literature, which changes the meaning slightly from our previous notion of constant in this class.

3. **Action** - $action.expr$: The action expression (also called prefix in the literature) means the process can perform an $action$ to get to the process $expr$. It will then continue on as $expr$.

4. **Summation** - $expr + expr$: This expression means we can choose between either process and continue forward. Once one process expression is chosen, the other one is discarded. As a note, the literature will sometimes use $\sum$ to represent multiple sums. In this lecture, we will only talk about binary summing.

5. **Composition** - $expr | expr$: The fifth expression means we can run both processes at the same time.

6. **Restriction** - $expr \backslash label$: This expression restricts the action $label$ and its complement from being performed, though it can be performed with the internal action $\tau$. For example, if $label$ was $s$, $s$ and $\bar{s}$ wouldn't be available to be performed. Similarly, if $label$ was $\bar{s}$, $\bar{s}$ and $s$ would not be available to be executed.

7. **Relabel** - $expr[label:label]$: The final expression relabels a given label in an expression to another label. Literature will sometimes show this as $expr[f]$ where $f: label \mapsto label$. However, in this lecture we will use our syntax because it is easier to manage and doesn't require us to keep track of another component $f$.

Now that we have defined the syntax, we need to define the transition system that explains how we get from one state to another.

### Semantics
First, we need to define what we mean by our labelled transition system. We can small step from one process expression $expr_1$ to another process expression $expr_2$ through a given $action$. We would denote this transiton as $expr_1 \xrightarrow{action} expr_2$.

We can now define our semantics.

1. **Skip** - $skip$: We won't have any semantics for skip since by definition it "does nothing".

2. **Constant** - $var \gets expr$: We will have just one rule for constant, which is that if we store an expression as a variable and that process can step to another process, then the variable can step to that process as well.
$$
\frac{A \leftarrow P \land P \xrightarrow{a} P'}
{A \xrightarrow{a} P'} 
\: \textrm{Con}
$$

3. **Action** - $action.expr$: Our action rule simply says we we can transition to the state through that action if it tells us we can.
$$
\frac{\texttt{ }}
{a.P \xrightarrow{a} P} 
\: \textrm{Act}
$$

4. **Summation** - $expr + expr$: We will have two summation rules. These rules say if one of the processes in the binary sumamtion can step to another process expression via an action, then the sum of the two can step to that process via the action. These two are represented for the left and right component of the sum
$$
\frac{P_1 \xrightarrow{a} P_1'}
{(P1 + P2) \xrightarrow{a} P_1'} 
\: \textrm{SumLeft}
$$

$$
\frac{P_2 \xrightarrow{a} P_2'}
{(P1 + P2) \xrightarrow{a} P_2'} 
\: \textrm{SumLeft}
$$

5. **Composition** - $expr | expr$: This one will have three rules. The first two rules are for each component of the expression. These rules say that if one of the processes can step to another process via a given action, then the entire composition can step to the new process on one side using that action. <br><br>The third rule defines what happens when the simultaneous actions of each expression interact with each other and change state simultaneously. This state change is internal to the composition, so we will use the internal action (also referred to as a perfect action) $\tau$.
$$
\frac{P_1 \xrightarrow{a} P_1'}
{(P1 | P2) \xrightarrow{a} (P_1' | P_2)} 
\: \textrm{ComRight}
$$
$$
\frac{P_2 \xrightarrow{a} P_2'}
{(P1 | P2) \xrightarrow{a} (P_1 | P_2')} 
\: \textrm{ComLeft}
$$

$$
\frac{P_1 \xrightarrow{a} P_1' \land P_2 \xrightarrow{\bar{a}} P_2'}
{(P1 | P2) \xrightarrow{\tau} (P_1' | P_2')} 
\: \textrm{ComInternal}
$$

6. **Restriction** - $expr \backslash label$: There is one restriction semantic. It essentially says the action is step is preserved as long as it wasn't restricted from being used.
   
$$
\frac{P_1 \xrightarrow{a} P_1' \land a \neq b \land \bar{a} \neq b}
{P_1\backslash b \xrightarrow{a}P_1'\backslash b} 
\: \textrm{Res}
$$

7. **Relabel** - $expr[label:label]$: The relabel semantics simply says if we can get from one process to another via an action, then we can get from that state to another using the relabeled action. We need to make sure the second process preserves the relabelling as well.
$$
\frac{P_1 \xrightarrow{a} P_1'}
{P_1[a:b] \xrightarrow{b}P_1'[a:b]} 
\: \textrm{Rel}
$$

We have now defined a complete list of semantics needed to make any transition. We do need to also define our order of operations. Our "PEMDAS" will be prioritized as following
  - Restriction and relabelling
  - Constant
  - Composition
  - Summation

### Example
Let's do a quick example to make sure we understand how to use CSS without value passing. We will take our example from Milner's Communication and Concurrency textbook.

Let's look at the following expression and attempt to justify it
$$
((a.E + b.skip)|\bar{a}.F)\backslash a \xrightarrow{\tau} (E | F)\backslash a
$$

First, we can deduce that the restriction rule is being applied.

$$
\frac{((a.E + b.skip)|\bar{a}.F) \xrightarrow{\tau} (E | F)}
{((a.E + b.skip)|\bar{a}.F)\backslash a \xrightarrow{\tau} (E | F)\backslash a}
\: \textrm{Rel}
$$

Then, we can see the internal composition rule is being applied which is why we are using $\tau$ as the action.
$$
\frac{
    \frac{\bar{a}.F \xrightarrow{\bar{a}} F \land (a.E + b.skip) \xrightarrow{a} E}
    {((a.E + b.skip)|\bar{a}.F) \xrightarrow{\tau} (E | F)}
    \: \textrm{ComInternal} 
}
{((a.P + b.skip)|\bar{a}.F)\backslash a \xrightarrow{\tau} (E | F)\backslash a}
\: \textrm{Rel}
$$

Let's focus on the left term. This is simply the action rule.
$$
\frac{
    \frac{
        \frac{}{\bar{a}.F \xrightarrow{\bar{a}} F} 
        \: \textrm{Act} 
        \land (a.E + b.skip) \xrightarrow{a} E}
    {((a.E + b.skip)|\bar{a}.F) \xrightarrow{\tau} (E | F)}
    \: \textrm{ComInternal} 
}
{((a.E + b.skip)|\bar{a}.F)\backslash a \xrightarrow{\tau} (E | F)\backslash a}
\: \textrm{Rel}
$$

Then, the right term is a sum, so we can apply one of the sum rules. Since $skip$ by definition doesn't transition, this means we are looking at the other term.
$$
\frac{
    \frac{
        \frac{}{\bar{a}.F \xrightarrow{\bar{a}} F} 
        \: \textrm{Act} 
        \frac{a.E \xrightarrow{a} E}{(a.E + b.skip) \xrightarrow{a} E}
        \: \textrm{SumLeft}  
        }
    {((a.E + b.skip)|\bar{a}.F) \xrightarrow{\tau} (E | F)}
    \: \textrm{ComInternal} 
}
{((a.E + b.skip)|\bar{a}.F)\backslash a \xrightarrow{\tau} (E | F)\backslash a}
\: \textrm{Rel}
$$

Finally, this term is just applying the action rule. Our final result is
$$
\frac{
    \frac{
        \frac{}{\bar{a}.F \xrightarrow{\bar{a}} F} 
        \: \textrm{Act} 
        \frac{
            \frac{}{a.E \xrightarrow{a} E} \: \textrm{Act} 
            }{(a.E + b.skip) \xrightarrow{a} E}
        \: \textrm{SumLeft}  
        }
    {((a.E + b.skip)|\bar{a}.F) \xrightarrow{\tau} (E | F)}
    \: \textrm{ComInternal} 
}
{((a.E + b.skip)|\bar{a}.F)\backslash a \xrightarrow{\tau} (E | F)\backslash a}
\: \textrm{Rel}
$$

That is how we can apply the CCS rules to various non-value passing expressions.

What we looked at so far is the "no value passing" CCS. There is also a value passing CCS that can be used if we add a few extensions. However, we are instead going to look at the next topic: $\pi$-Calculus.

## $\pi$-Calculus
$\pi$-Calculus builds off of CCS. One of the large benefits of it is that you can type it; however, we will just be looking at the untyped form. We will be adding the passing of values through channels.

### Syntax
We will start by defining the syntax of $\pi$-calculus. Similar to CCS, we need to define $var$ and the $label$s.
```
var := string

label := in 
    | out
```

We now need to define the actions like we did in CCS. Our CCS did not involve value passing, but $\pi$-calculus will. Therefore, we need a way to "pass" data through actions or channels.

Now, we can define the actions, which will be similar
```
action := In in label
    | Out out label
    | Tau
```

For example, $In a x$ receives the value $x$ through channel $a$. $x$ is a placeholder for the value received just as it is a placeholder in a function $f(x)$. On the other hand, $Out \bar{a} x$ would mean data $x$ is passed out of channel $\bar{a}$. Finally, $Tau$ is the same as it was in CCS where it stands for an internal action.

Next, we can look at the agent expressions that can be used. This will look quite similar to CCS, though the functionality will be different once we get into it.

```
expr := skip
    | action.expr
    | expr + expr
    | expr | expr
    | Nu label expr
```

We also need the ability to define a process, which may have multiple input variables. We will use the list we created earlier in the semester, but this time we will pass it $label$ instead of $nat$.

```
list_labels := nil 
    | Cons label list_labels
```

We are now ready to add the constructor to $expr$.

```
expr := skip
    | var list_labels <- expr
    | action.expr
    | expr + expr
    | expr | expr
    | Nu label expr
```

We can also add if statements and the such, but in this lecture we will attempt to make it as clear as possible and reduce some of the noise.

We can now define these expressions, though many of them will be quite similar if not identical to CCS.

1. **Skip** - $skip$: This will be identical to CCS.

2. **Constant** - $var list_labels \gets expr$: This is quite similar to CCS, though we need to be able to "pass in data". In CCS, we would define a process like $A \gets expr$, but now we need to define a process like $A(x_1, x_2, \dots, x_n) \gets expr$ because data can be passed into the process. The $list_labels$ allows us to do that.

3. **Action** - $action.expr$: This is nearly identical to CCS. The exception here, is we are able to pass variables in and out via channels. We described this above, but to quickly reiterate, $(In a x).P$ would mean "receive $x$ through the channel $a$ and then proceed as $P$". On the other hand, $(Out \bar{a} x).P$ would mean "pass the value $x$ to $\bar{a}$ and then proceed as $P$. In the same way of CCS, we can think of these as in and out ports, but now they receive data. 

4. **Summation** - $expr + expr$: This will be identical to CCS.

5. **Composition** - $expr | expr$: This will be identical to CCS.

6. **Restriction** - $Nu label expr$: While this is the same general idea as CCS, it has semantics and so we changed the notation to emphasize that. In the same way as before, it changes $label$ to be internal to the $expr$. 

Now, on to the semantics so we know how the syntax can behave!

### Semantics



We are now ready to write out our semantics. Just like in CCS, we will not have one for $skip$.

1. **Structural Congruence**: This first rule is based on the concept of structural congruence. One of the big differences with $\pi$-calculus is we can have syntactically different expressions that represent the same behavior. For example, 
$(In \texttt{ } a \texttt{ } x).(Out \texttt{ } \bar{b} \texttt{ } x)$ is bounded by $x$ but performs the same behavior as $(In \texttt{ } a \texttt{ } y).(Out \texttt{ } \bar{b} \texttt{ } y)$ which is bounded by $y$. Similarly, $P | Q$ and $Q | P$ are intuitively the same, even though they have different syntax. We need a way to define expressions that have the same meaning but different syntax, and we can do that with structural congruence. We will use $\equiv$ to denote two expressions that are structurally the same.
<br>The rules of structural congruence that we will be covering are defined as follows:
   - **Alpha Conversions**: This is like our original definition. Two expressions are congruent if they only differ in their bounded name. For example, $(In \texttt{ } a \texttt{ } x).(Out \texttt{ } \bar{b} \texttt{ } x) \equiv (In \texttt{ } a \texttt{ } y).(Out \texttt{ } \bar{b} \texttt{ } y)$.
   - **Parallel Congruence** - $P | Q \equiv Q|P$, $(P|Q)|R \equiv P|(Q|R)$, and $P|0 \equiv P$: Intuitively, we know that running two agents concurrently doesn't have an order. We also know running a process concurrently with something that can't run is equivalent to just running the original process.
   - **Summation Congruence** - $P + Q \equiv Q+P$, $(P+Q)+R \equiv P+(Q+R)$, and $P+0 \equiv P$: This is the same as parallel congruence but for summation. This makes sense since we are choosing between two processes and it doesn't matter the order in which they are presented to us. Additionally, if we are choosing between a process and nothing, we have to choose the process.
   - **Unfolding Law** - $A(y) \equiv P{y/x}$ if $A (const x nil) <- P$: In other words, when we put a value in for a defined constant, we can simply substitute that value in for the "placeholder" value.
  
    We are now ready to define our step rule related to structural congruence. This rule says if saying "if $a$ is congruent to $b$, $b$ can step to $c$, and $c$ is congruent to $d$, then $a$ can step to $d$".
    $$
\frac{P' \equiv P \land P \xrightarrow{a} Q \land Q \equiv Q'}
{P' \xrightarrow{a} Q'} 
\: \textrm{Struct}
$$

2. **Action** - $action.expr$: This is the same as in CCS, but we will rewrite it for completeness.
$$
\frac{\texttt{ }}
{a.P \xrightarrow{a} P} 
\: \textrm{Act}
$$

3. **Summation** - $expr + expr$: This is equivalent to CCS as well. The only difference is we can now apply the structural congruence rule to convert an expression $A + B$ to $B+A$; therefore, we don't need two rules and can just use one.
$$
\frac{P_1 \xrightarrow{a} P_1'}
{(P1 + P2) \xrightarrow{a} P_1'} 
\: \textrm{Sum}
$$


4. **Composition** - $expr | expr$: Because of the structural congruence law, we don't need a "left" and "right" for composition - one will suffice. That being said, the passing of data adds some complication to the composition rule. Specifically, the issue arises when it comes to free and bound variables. The "in" ports and restrictions bind variables and the "out" ports are free variables. We can define the free variables with the function $free(a)$ and we can define the bound variables as $bound(a)$. When we take composition into account, we need to modifying the free variables in the side that is not stepping.
<br>$ComInternal$ is the same as it was in CCS. 
$$
\frac{P_1 \xrightarrow{a} P_1' \land free(P2) \cap bound(a) = \empty}
{(P1 | P2) \xrightarrow{a} (P_1' | P_2)} 
\: \textrm{ComExternal}
$$

$$
\frac{P_1 \xrightarrow{a} P_1' \land P_2 \xrightarrow{\bar{a}} P_2'}
{(P1 | P2) \xrightarrow{\tau} (P_1' | P_2')} 
\: \textrm{ComInternal}
$$

5. **Restriction** - $Nu label expr$: This is the same as CCS, except we have to change $\neq$ to $\notin$ to account for the passing of data.
   
$$
\frac{P_1 \xrightarrow{a} P_1' \land a \notin b \land \bar{a} \notin b}
{P_1\backslash b \xrightarrow{a}P_1'\backslash b} 
\: \textrm{Res}
$$

And that is our introduction to CCS and $\pi$-Calculus!