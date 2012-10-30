/**
 * A wall piece on the board, untouchable obstacle. 
 */
final class Wall implements BoardItem
{

  final /*@ spec_public */ Position position;

  /** @informal: the constructed object has the given position. */
  //@ ensures position == p;
  Wall (Position p) {
    position = p;
  }

  /** @informal: we cannot stand on the wall */
  //@ also ensures \result == false;
  public boolean isCanStepOn () {
    return false;
  }

  /** @informal: the wall cannot be moved */
  //@ also ensures \result == false; 
  public boolean isMovable () {
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


  /** @informal: walls are not marked */
  //@ also ensures \result == false; 
  public boolean isMarked () {
    return false;
  }

  public String toString () {
    return "wall(" + position.x + "," + position.y + ")";
  }

}
