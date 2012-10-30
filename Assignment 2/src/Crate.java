/**
 * A crate on the board that can be moved, that is not standing on a marked position. 
 */
public class Crate implements BoardItem
{

  Position position;

  /** @informal: the constructed object has the given position. */
  Crate (Position p) {
    position = p;
  }

  /** @informal: we cannot stand on crates */
  public boolean isCanStepOn () {
    return false;
  }

  /** @informal: crates can be moved */
  public boolean isMovable () {
    return true;
  }

  /** @informal: we return our position */
  public Position position () {
    return position;
  }

  public void setPosition (Position newPosition)
      throws IllegalStateException {
    if (position.isValidNextPosition (newPosition)) {
      position = newPosition;
    } else {
      throw new IllegalStateException ();
    }
  }

  /** @informal: particular instances of a crate are marked, we are not */
  public boolean isMarked () {
    return false;
  }

  public String toString () {
    return "crate(" + position.x + "," + position.y + ")";
  }

}
