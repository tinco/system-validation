/**
 * A crate on the board that can be moved, and is standing on a marked position. 
 */
public final class MarkedCrate extends Crate
{

  MarkedCrate (Position p) {
    super (p);
  }

  /** @informal: this kind of crate is marked */
  public boolean isMarked () {
    return true;
  }

  public String toString () {
    return "crateX(" + position.x + "," + position.y + ")";
  }

}
