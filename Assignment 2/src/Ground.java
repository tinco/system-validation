/**
 * A piece of unmarked ground. 
 */
class Ground implements BoardItem
{

  final /*@ spec_public*/ Position position;

  /** @informal: the constructed object has the given position. */
  //@ ensures position == p;
  Ground (Position p) {
    position = p;
  }

  /** @informal: we can stand on the ground */

  //@ also ensures \result == true; 
  public boolean isCanStepOn () {
    return true;
  }

  /** @informal: we cannot move ground */
  //@ also ensures \result == false; 
  public boolean isMovable () {
    return false;
  }

  /** @informal: particular instances of a ground are marked, we are not */
  //@ also ensures getClass().getName() == "Ground" ==> \result == false;
  public boolean isMarked () {
    return false;
  }

  /** @informal: we return our position */
  //@ also ensures \result == position;
  public Position position () {
    return position;
  }

  public void setPosition (Position newPosition)
      throws IllegalStateException {
    throw new IllegalStateException ();
  }

  public String toString () {
    return "ground(" + position.x + "," + position.y + ")";
  }

}
