/**
 * A wall piece on the board, untouchable obstacle. 
 */
final class Wall implements BoardItem
{

  final Position position;

  /** @informal: the constructed object has the given position. */
  Wall (Position p) {
    position = p;
  }

  /** @informal: we cannot stand on the wall */
  public boolean isCanStepOn () {
    return false;
  }

  /** @informal: the wall cannot be moved */
  public boolean isMovable () {
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


  /** @informal: walls are not marked */
  public boolean isMarked () {
    return false;
  }

  public String toString () {
    return "wall(" + position.x + "," + position.y + ")";
  }

}
