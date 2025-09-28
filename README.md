# Time loop calculus

A minimal language / calculus for exploring paradoxical fixed points.

```py
if v == 'x':
    'y'
else:
    'x'
```

The function above has no standard fixed point (a value `v` where `v` equals `f(v)`) since it turns 'x' into 'y' and 'y' into 'x'. Time loop calculus solves this by introducing "time loop" values that represent sequences of values oscillating over discrete time steps.

The value `['x'; 'y']` represents a time loop that is 'x' at step 0, 'y' at step 1, 'x' at step 2, and so forth. This allows us to find fixed points for paradoxical functions like the liar's paradox.

When comparing a time loop to an atomic value, the atomic value is conceptually extended into a constant time loop. So `['x'; 'y'] == 'x'` evaluates to `[true; false]`, creating a time-looped boolean that can be used in conditionals.

For nested paradoxes, time loops can contain other time loops. The value `[['x'; 'y']; ['z']]` has depth 2, where the inner loops are compared against lifted outer values to maintain compositional reasoning.

All time loops follow the same conceptual clock, allowing multiple subexpressions that depend on the same fixed point to remain synchronized. This enables compositional analysis of complex paradoxical functions.

The implementation handles time loop shifting to ensure proper fixed point semantics, though the exact shifting mechanism is still being refined.

Here are a few examples:

## Simple identity

```
if 'x' == 'x':
    'x'
else:
    'y'
```

**Fixed point:** `'x'`

## Simple liar

```
if ['x'; 'y']@0/2 == 'x':
    'y'
else:
    'x'
```

**Fixed point:** `['x'; 'y']@0/2`

## Captured liar

```
if [['x']; ['y'; 'x']]@0/2 == ['x'; 'y']:
    'y'
else:
    'x'
```

**Fixed point:** `[['x']; ['y'; 'x']]@0/2`

## Escaped liar

```
if [['x']; ['x'; 'y']]@0/2 == ['x'; 'y']:
    'x'
else:
    if [['x']; ['x'; 'y']]@0/2 == 'x':
        'y'
    else:
        'x'
```

**Fixed point:** `[['x']; ['x'; 'y']]@0/2`

## Liar's twin

```
if ['x'; 'y']@0/2 == 'x':
    'y'
else:
    if ['x'; 'y']@0/2 == 'x':
        'y'
    else:
        'x'
```

**Fixed point:** `['x'; 'y']@0/2`
