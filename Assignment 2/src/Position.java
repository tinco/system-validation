/**
 * Stores coordinates of the position on the board.
 */
final class Position
{


  int x;
  int y;

  /** @informal: the position canno be negative */

  /** @informal: the constructed object has the given position values,
         that need to be valid in the first place. */
  Position (int x, int y) {
    this.x = x;
    this.y = y;
  }

  /** @informal: we only allow to compare to non null object of
         our own class. The comparison is successful if and only if both
         coordinates match. */
  public boolean equals (/*@ nullable @*/ Object o) {
    if (o instanceof Position) {
      Position q = (Position) o;
      return x == q.x && y == q.y;
    }
    return false;
  }

  /** @informal: check if the new position is a valid one step horizontal or
         vertical move from the current one. */
  /*@ pure */ /*@ spec_public @*/ boolean isValidNextPosition (Position newPosition) {
    if (newPosition.x == x) {
      return newPosition.y == y + 1 || newPosition.y == y - 1;
    } else if (newPosition.y == y) {
      return newPosition.x == x + 1 || newPosition.x == x - 1;
    }
    return false;
  }

  public String toString () {
    return "position(" + x + "," + y + ")";
  }

}
