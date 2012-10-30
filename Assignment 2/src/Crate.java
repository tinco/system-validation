/**
 * A crate on the board that can be moved, that is not standing on a marked position. 
 */
public class Crate implements BoardItem
{

  /*@ spec_public */ Position position;

  /** @informal: the constructed object has the given position. */
  //@ ensures position == p;
  Crate (Position p) {
    position = p;
  }

  /** @informal: we cannot stand on crates */
  //@ also ensures \result == false;
  public boolean isCanStepOn () {
    return false;
  }

  /** @informal: crates can be moved */
  //@ also ensures \result == true;
  public boolean isMovable () {
    return true;
  }

  /** @informal: we return our position */
  //@ also ensures \result == position;
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
  //@ also ensures getClass().getName() == "Crate" ==> \result == false;
  public boolean isMarked () {
    return false;
  }

  public String toString () {
    return "crate(" + position.x + "," + position.y + ")";
  }

}
