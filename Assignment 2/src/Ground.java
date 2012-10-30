/**
 * A piece of unmarked ground. 
 */
class Ground implements BoardItem
{

  final Position position;

  /** @informal: the constructed object has the given position. */
  Ground (Position p) {
    position = p;
  }

  /** @informal: we can stand on the ground */
  public boolean isCanStepOn () {
    return true;
  }

  /** @informal: we cannot move ground */
  public boolean isMovable () {
    return false;
  }

  /** @informal: particular instances of a ground are marked, we are not */
  public boolean isMarked () {
    return false;
  }

  /** @informal: we return our position */
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
