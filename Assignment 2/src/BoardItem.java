/**
 * Represents an item on the board that occupies one cell. Can
 * be either a piece of the wall (unmovable, cannot be stepped on),
 * a crate (movable, cannot be stepped on), ground (unmovable, can be stepped on).
 * Additionally each crate or ground can be marked. 
 */
public interface BoardItem
{

  /*@ pure */ boolean isMovable ();

  /*@ pure */ boolean isCanStepOn ();

  /*@ pure */ boolean isMarked ();

  /** @informal: We cannot move ground  */
  //@ public invariant this instanceof Ground ==> !isMovable();

  /** @informal: Something that can be moved cannot be stepped on */
  //@ public invariant isMovable() ==> !isCanStepOn();

  /** @informal: Only ground and crates can be marked */
  //@ public invariant !(this instanceof Ground) && !(this instanceof Crate)  ==> !isMarked();

  public /*@ pure */ Position position ();

  /**
    * @informal: 
    *  - Only movable items can change their position. 
    *  - The position can be only changed by one increment in only
    *    one direction, class Position has a method to check that.
    *  - For all situations when the position cannot be changed
    *    an exception is thrown and the position indeed stays the 
    *    fixed.
    *  - For valid position changes the new position is in effect.
    */
  //@ requires isMovable();
  //@ requires position().isValidNextPosition(newPosition);
  //@ ensures  position() == newPosition;
  //@ also
  //@ requires !isMovable();
  //@ requires !position().isValidNextPosition(newPosition);
  //@ signals_only IllegalStateException;
  //@ ensures position() == \old(position());
  void setPosition (Position newPosition)
      throws IllegalStateException;

}
