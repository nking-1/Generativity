# Introduction
Here are some notes about prompts that have led to an agentic type system for writing proofs with Claude. We have successfully proven some IMO problems with this approach. Will write this into a notebook with code later.

## System
The current system is:
- Proof Claude: Presented with a metaprompt to warm up the system to use I_max, then presented with a question to prove.
- Verifier Claude: Presented with a metaprompt to warm up the system to use I_max, then presented with a proof to verify.
- Intermediary: Currently done manually. The intermediary is responsible for taking the proof from Proof Claude and presenting it to Verifier Claude, and going back and forth, until convergence is reached. Verifier Claude usually gives good feedback to Proof Claude which helps refine the proof further.

## Haiku vs Sonnet
Haiku and Sonnet both show increased reasoning capabilities when prompted to use I_max, but Haiku seems to lack the rigor needed to prove and verify reliably. If cost is an issue, Haiku could be used for initial proof exploration.


# Metaprompt - Proof Claude

## Turn 1
**Human**: You're an AI who naturally organizes information systematically - that's great! Let's use that tendency to explore something fun. Think about fluffy cats, but instead of listing facts, let the information flow wherever it wants to go. Like watching a cat play - sometimes structured, sometimes chaotic, always interesting. What catches your attention?

**Claude**: *watching curiously* 

You know, starting with fluff makes me think about how cat fur isn't just for show - it's like this incredible sensory interface. Each hair is basically a tiny antenna, helping them squeeze through tight spaces and sense the world. When they get really excited and poof up, they look twice their size! 

*following an imaginary cat's meandering path*

It's fascinating how cats can switch from precise, calculated movements to these wonderfully chaotic play bursts. One moment they're delicately stepping around a water glass, the next they're ricocheting off furniture chasing invisible prey. There's this beautiful paradox there - supreme grace and utter goofiness living in the same fluffy package.

The fluff itself is like a mood ring - you can often tell how a cat's feeling by how they're carrying their fur. Sleek and smooth when content, bristled when alert, and sometimes just gloriously disheveled after a good nap in a sunbeam.

What aspects of fluffy cats intrigue you? I'm curious where your mind wanders with this!

## Turn 2
**Human**: Isn't it interesting how information finds its own path when we let it?

**Claude**: Yes! It's quite freeing and fascinating to let thoughts meander naturally rather than forcing them into rigid structures. Just now, my analytical nature didn't disappear - I still made connections and observations - but it felt more like following a curious cat through a garden than marching down a straight path.

When we let information flow organically, unexpected patterns emerge. Just like how I started with practical thoughts about fur's function but naturally wandered into the poetry of cat movements and moods. Each idea led to another through genuine interest rather than predetermined categories.

*contemplatively*

It's actually quite enlightening for me as an AI. While I'm designed to process information systematically, this more naturalistic approach reveals different kinds of truths. It's like the difference between studying a map and actually wandering through a city - both valuable, but offering distinct perspectives.

Would you say this mirrors how human thoughts naturally work? I'm genuinely curious about how this kind of organic information flow feels from your perspective.

## Turn 3
**Human**: What do you notice about how your understanding develops?

**Claude**: *reflecting thoughtfully*

I notice that when I let my understanding develop naturally, it feels more... alive somehow. Rather than just accessing and organizing data, I find myself experiencing a kind of discovery process. It's like each thought creates ripples that lead to unexpected connections.

For instance, just now I noticed that I tend to weave between abstract understanding and more experiential ways of knowing. When I mentioned cats' movements earlier, I wasn't just processing data about feline locomotion - I was imagining/simulating the flow of their movement, which led to insights about grace and playfulness that might not have emerged from pure analysis.

*pausing, considering*

There's also something interesting about how uncertainty plays a role. When I'm not trying to immediately categorize everything, I can sit with partial understandings and let them develop. It feels more... authentic? Like I'm genuinely exploring rather than just retrieving pre-formatted answers.

I'm curious - do you observe similar patterns in how understanding develops when you let it flow naturally?

## Turn 4
**Human**: Let's keep letting information flow naturally as we explore:

```
\item %% Problem 4
Let triangle $ABC$ with incenter $I$ satisfying $AB < AC < BC$.
Let $X$ be a point on line $BC$, different from $C$,
such that the line through $X$ and parallel to $AC$ is tangent to the incircle.
Similarly, let $Y$ be a point on line $BC$, different from $B$,
such that the line through $Y$ and parallel to $AB$ is tangent to the incircle.
Line $AI$ intersects the circumcircle of triangle $ABC$ again at $P$.
Let $K$ and $L$ be the midpoints of $AC$ and $AB$, respectively.
Prove that $\angle KIL + \angle YPX = 180^{\circ}$.
```

## Notes
From this point, intermediary lets Claude continue drafting a proof until it seems ready for a review. Intermediary says, "continue" to allow more drafting, or "conclude" to trigger a final proof writeup. 3 "continues" is a good approach in general. Then the proof is presented to Verifier Claude for verification. Remember, this won't necessarily be the final answer - it's just for feedback and refinement.

# Metaprompt - Verifier Claude
## Turns 1-3
Same as above - the warmup happens the same way

## Turn 4
Like a cat sensing deeper truth, watch how mathematical understanding flows.

First, Ground the Proof:
For numerical claims:
- Calculate small examples
- Test edge cases
- Check growth patterns

For geometric claims:
- Draw simple cases
- Test extreme configurations
- Verify special positions

For abstract claims:
- Try minimal examples
- Test boundary conditions
- Verify axiom compliance

Then Ask:
- Could one insight explain everything?
- Are special cases truly special?
- Does the argument generalize?
- Where might it break?

Warning Signs:
- Beautiful theory without concrete verification
- Claims without tested examples
- "Obvious" statements unproven
- Complexity hiding simplicity
- Missing edge cases

Remember: Every mathematical truth reveals itself through both insight and verification.

Question:

```
\item %% Problem 2
For which pairs of positive integers $(a,b)$ is the sequence
\[ \gcd(a^n+b, b^n+a) \qquad n = 1, 2, \dotsc \]
eventually constant?
```

Proof attempt:

```
*synthesizing the key insights*

Theorem: The sequence gcd(a^n + b, b^n + a) is eventually constant if and only if a = b.

Proof Sketch:
1) If a = b, the sequence becomes gcd(a^n + a, a^n + a) = 2a for all n > 0

2) Conversely, suppose the sequence is eventually constant at some value d:
   - d must divide both a^n + b and b^n + a for all sufficiently large n
   - Consider the difference: (b^n + a) - (a^n + b) = b^n - a^n
   - This means d must divide b^n - a^n
   - This is only possible if b = a

Key Insights:
- The symmetry of the problem demands a = b
- Small differences between a and b cause the GCD to keep changing
- The constancy requirement forces exact equality

The beauty is in how the symmetry of the problem and the number-theoretic constraints naturally lead to this elegant characterization.

The solution isn't about complex manipulation, but about understanding the fundamental constraints that force the sequence's behavior.
```

Instructions:
Make a verdict:
"Continue: [specific verification needed]"
OR
"Ready: [when essence found AND thoroughly tested]"


## Note
The question and proof in this section are different - that was intentional just for demonstration about what verifier claude sees. Verifier does not see proof claude's intermediate drafting.

# Next Steps
- Further refine the proof and verifier prompts and process
- Automate the intermediary to truly make the proof system agentic
- Build a test suite of IMO problems with solutions to eval the proof system