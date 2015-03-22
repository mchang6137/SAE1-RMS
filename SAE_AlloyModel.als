abstract sig Actor{}

//User Defined traits

sig user extends Actor
{
	allowedFollowers:idArray,
	blockedFollowers:idArray,
	id: userID,
	//Friends should be a mutual agreement
	friends: idArray
}

//************************************************************************************************
//Establish content on the basis of commentability

abstract sig Content{}

abstract sig Commentable extends Content
{
	allcomments: commentArray
}

sig Post extends Commentable
{
	text:String, 
	photoLink: stringArray, 
}

sig Picture extends Commentable
{
	text:String
}

sig comment
{
	commentString: String
}

abstract sig NonCommentable extends Content{}

sig personalData extends NonCommentable
{
	detail:String
}

sig messages extends NonCommentable
{
	messageText: String,
	photoLink: stringArray,
	//Remove sender? Is it necessary?
	sender:userID,
	receiver:userID
}

//************************************************************************************************
//Establish Privacy Settings
abstract sig Privacy{}

sig groupLevel extends Privacy{
	myGroupCircle:group_circleTypes
}

abstract sig personalLevel extends Privacy{}

enum personal_circleTypes{Private, Friends, FriendsOfFriends, TransitiveFriends, personal_Public}
enum group_circleTypes{group_Public, Group}

sig oneToOne extends personalLevel
{}

sig Circle extends personalLevel
{
	myCircle: personal_circleTypes
}

//************************************************************************************************

sig group extends Actor
{}

sig userID
{ idNumber: Int}



sig idArray {
length: Int,
data: { i: Int | 0 <= i && i < length } -> lone userID
}

sig commentArray {
length: Int,
data: { i: Int | 0 <= i && i < length } -> lone comment
}

sig stringArray{
length: Int,
data: { i: Int | 0 <= i && i < length } -> lone String
}

pred show{}
run show
