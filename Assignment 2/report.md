Tinco Andringa (s0159786)

System Validation Assignment 2
==============================


Lock requirements
-----------------

### Both doors are not open at the same time

We assume the doors are modeled as modules with an open property that tells
wether they are open. The specification in LTLSpec:

    G !(door1.open & door2.open)

### Allow at least one ship to pass eventually

We assume a ship is modeled as a module, with a property position that is defined by the enumeration
`{before, in, after}` that are set to the position the ship is in relative
to the lock and the direction it is going in.

    G (ship.before -> F ship.after)

This specification is more strict than 'at least one' in that it guarantees
that every ship entering the lock will eventually pass it instead of
just one of them. In my opinion that makes more sense as a lock requirement.

In CTLSpec making sure it is possible at least one ship to pass would be:

    EF (ship.after)

### Only open the door if the water levels are equal

We assume the doors are modeled as modules with a can_open
that guards the opening of that door. The lock also
has three parts, left, middle and right, that have a water_level
property that can have values from the enum `{low, high}`.

    G ((door1.can_open -> left.water_level = middle.water_level) &
       (door2.can_open -> middle.water_level = right.water_level))

### The doors should not open or close without any ships waiting

We assume that the parts of the lock also have an occupied property
that indicates wether a ship is waiting there. The doors also have
properties opening and closing.

    G ((door1.opening | door1.closing -> left.occupied | middle.occupied) &
       (door2.opening | door2.closing -> right.occupied | middle.occupied))

### Boats should pass in order of arrival

We assume that every ship has a number that is assigned to it when
it enters the queue for the lock. The number is equal to the amount
of ships that have entered the queue for the lock thus far.

We also assume the lock has a list of all boats currently waiting in or
before the lock called `waitingShips`.

The lock has the following specification for the pass method that gets called
to remove a ship from the lock when it has passed in JML.

    //@ requires \forall Ship otherShip; waitingShips.has(otherShip); otherShip.number > ship.number

### It should be possible to adjust the waterlevel

We assume that there is a property water_level_adjustable. In CTLSpec:

    G (water_level_adjustable)

This is hardly a useful property for the system. At the very least it is
a dangerous property. A better property would be, the water level should
only be adjustable when both doors are closed, like so:

    G (water_level_adjustable -> door1.closed & door2.closed)

This property protects the doors and the ships against water damage.

### Do not close the door while a ship is leaving

We assume that there is a property on the lock called direction that denotes
wether the ships currently being served are going from left to right or
from left to right.

    G (( direction = leftToRight & middle.occupied -> door2.can_close = false) &
       ( direction = rightToLeft & middle.occupied -> door1.can_close = false))

This assumes that with leaving it is meant that the middle, the lock part, is being left.

JML Annotations
---------------

### i.


