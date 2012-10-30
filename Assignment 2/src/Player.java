/**
 * Represents a player. Technically, a player could be a board item, but we keep 
 * her/him separate. 
 */
final class Player
{

  Position position;

  /** @informal: the constructed object has the given position. */
  Player (Position p) {
    position = p;
  }

  /** @informal: we return our position */
  public Position position () {
    return position;
  }

  /** @informal: The player is not an instance of the BoardItem,
         so it needs to have its own specification for this method.
         The player requires a valid next position, 
         that is, next to the current position of the player.
         Then it gets the new position. */
  public void setPosition (Position newPosition) {
    position = newPosition;
  }

  public String toString () {
    return "player(" + position.x + "," + position.y + ")";
  }

}
