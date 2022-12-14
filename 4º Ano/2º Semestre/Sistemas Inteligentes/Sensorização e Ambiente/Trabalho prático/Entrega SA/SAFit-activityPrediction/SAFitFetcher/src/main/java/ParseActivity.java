import org.json.JSONArray;
import org.json.JSONObject;
import org.joda.time.DateTime;

import java.util.*;

public class ParseActivity {
    public static List<String> parse(String responseBody) {
        Map<Integer, String> types = new HashMap<Integer, String>();

        types.put(9,"Aerobics");
        types.put(119,"Archery");
        types.put(10,"Badminton");
        types.put(11,"Baseball");
        types.put(12,"Basketball");
        types.put(13,"Biathlon");
        types.put(1,"Biking");
        types.put(14,"Handbiking");
        types.put(15,"Mountain biking");
        types.put(16,"Road biking");
        types.put(17,"Spinning");
        types.put(18,"Stationary biking");
        types.put(19,"Utility biking");
        types.put(20,"Boxing");
        types.put(21,"Calisthenics");
        types.put(22,"Circuit training");
        types.put(23,"Cricket");
        types.put(113,"Crossfit");
        types.put(106,"Curling");
        types.put(24,"Dancing");
        types.put(102,"Diving");
        types.put(117,"Elevator");
        types.put(25,"Elliptical");
        types.put(103,"Ergometer");
        types.put(118,"Escalator");
        types.put(26,"Fencing");
        types.put(27,"Football (American)");
        types.put(28,"Football (Australian)");
        types.put(29,"Football (Soccer)");
        types.put(30,"Frisbee");
        types.put(31,"Gardening");
        types.put(32,"Golf");
        types.put(122,"Guided Breathing");
        types.put(33,"Gymnastics");
        types.put(34,"Handball");
        types.put(114,"HIIT");
        types.put(35,"Hiking");
        types.put(36,"Hockey");
        types.put(37,"Horseback riding");
        types.put(38,"Housework");
        types.put(104,"Ice skating");
        types.put(0,"In vehicle");
        types.put(115,"Interval Training");
        types.put(39,"Jumping rope");
        types.put(40,"Kayaking");
        types.put(41,"Kettlebell training");
        types.put(42,"Kickboxing");
        types.put(43,"Kitesurfing");
        types.put(44,"Martial arts");
        types.put(45,"Meditation");
        types.put(46,"Mixed martial arts");
        types.put(108,"Other");
        types.put(47,"P90X exercises");
        types.put(48,"Paragliding");
        types.put(49,"Pilates");
        types.put(50,"Polo");
        types.put(51,"Racquetball");
        types.put(52,"Rock climbing");
        types.put(53,"Rowing");
        types.put(54,"Rowing machine");
        types.put(55,"Rugby");
        types.put(8,"Running");
        types.put(56,"Jogging");
        types.put(57,"Running on sand");
        types.put(58,"Running (treadmill)");
        types.put(59,"Sailing");
        types.put(60,"Scuba diving");
        types.put(61,"Skateboarding");
        types.put(62,"Skating");
        types.put(63,"Cross skating");
        types.put(105,"Indoor skating");
        types.put(64,"Inline skating (rollerblading)");
        types.put(65,"Skiing");
        types.put(66,"Back-country skiing");
        types.put(67,"Cross-country skiing");
        types.put(68,"Downhill skiing");
        types.put(69,"Kite skiing");
        types.put(70,"Roller skiing");
        types.put(71,"Sledding");
        types.put(73,"Snowboarding");
        types.put(74,"Snowmobile");
        types.put(75,"Snowshoeing");
        types.put(120,"Softball");
        types.put(76,"Squash");
        types.put(77,"Stair climbing");
        types.put(78,"Stair-climbing machine");
        types.put(79,"Stand-up paddleboarding");
        types.put(3,"Still (not moving)");
        types.put(80,"Strength training");
        types.put(81,"Surfing");
        types.put(82,"Swimming");
        types.put(84,"Swimming (open water)");
        types.put(83,"Swimming (swimming pool)");
        types.put(85,"Table tennis (ping pong)");
        types.put(86,"Team sports");
        types.put(87,"Tennis");
        types.put(5,"Tilting (sudden device gravity change)");
        types.put(88,"Treadmill (walking or running)");
        types.put(4,"Unknown (unable to detect activity)");
        types.put(89,"Volleyball");
        types.put(90,"Volleyball (beach)");
        types.put(91,"Volleyball (indoor)");
        types.put(92,"Wakeboarding");
        types.put(7,"Walking");
        types.put(93,"Walking (fitness)");
        types.put(94,"Nording walking");
        types.put(95,"Walking (treadmill)");
        types.put(116,"Walking (stroller)");
        types.put(96,"Waterpolo");
        types.put(97,"Weightlifting");
        types.put(98,"Wheelchair");
        types.put(99,"Windsurfing");
        types.put(100,"Yoga");
        types.put(101,"Zumba");
        List<String> data = new ArrayList<String>();

        JSONObject json  = new JSONObject(responseBody);
        JSONArray sessions = json.getJSONArray("session");
        for(Object obj : sessions){
            JSONObject fields = (JSONObject) obj;
            if(types.get(fields.getInt("activityType"))!=null) {
                StringBuilder sb = new StringBuilder();
                String startime = (String) fields.getString("startTimeMillis");
                sb.append(new DateTime(Long.valueOf(startime)));
                sb.append("; ");
                String endtime = (String) fields.getString("endTimeMillis");
                sb.append(new DateTime(Long.valueOf(endtime)));
                sb.append("; ");
                sb.append(types.get(fields.getInt("activityType")));
                data.add(sb.toString());
                sb.append("\n");
            }
        }
        //System.out.println(sb);
        return data;
    }

    public static List<Map.Entry<DateTime, DateTime>> intervals(String responseBody){
        List<Map.Entry<DateTime, DateTime>> intervals = new ArrayList<>();
        DateTime start,end;

        Map<Integer, String> types = new HashMap<Integer, String>();

        types.put(9,"Aerobics");
        types.put(119,"Archery");
        types.put(10,"Badminton");
        types.put(11,"Baseball");
        types.put(12,"Basketball");
        types.put(13,"Biathlon");
        types.put(1,"Biking");
        types.put(14,"Handbiking");
        types.put(15,"Mountain biking");
        types.put(16,"Road biking");
        types.put(17,"Spinning");
        types.put(18,"Stationary biking");
        types.put(19,"Utility biking");
        types.put(20,"Boxing");
        types.put(21,"Calisthenics");
        types.put(22,"Circuit training");
        types.put(23,"Cricket");
        types.put(113,"Crossfit");
        types.put(106,"Curling");
        types.put(24,"Dancing");
        types.put(102,"Diving");
        types.put(117,"Elevator");
        types.put(25,"Elliptical");
        types.put(103,"Ergometer");
        types.put(118,"Escalator");
        types.put(26,"Fencing");
        types.put(27,"Football (American)");
        types.put(28,"Football (Australian)");
        types.put(29,"Football (Soccer)");
        types.put(30,"Frisbee");
        types.put(31,"Gardening");
        types.put(32,"Golf");
        types.put(122,"Guided Breathing");
        types.put(33,"Gymnastics");
        types.put(34,"Handball");
        types.put(114,"HIIT");
        types.put(35,"Hiking");
        types.put(36,"Hockey");
        types.put(37,"Horseback riding");
        types.put(38,"Housework");
        types.put(104,"Ice skating");
        types.put(0,"In vehicle");
        types.put(115,"Interval Training");
        types.put(39,"Jumping rope");
        types.put(40,"Kayaking");
        types.put(41,"Kettlebell training");
        types.put(42,"Kickboxing");
        types.put(43,"Kitesurfing");
        types.put(44,"Martial arts");
        types.put(45,"Meditation");
        types.put(46,"Mixed martial arts");
        types.put(108,"Other");
        types.put(47,"P90X exercises");
        types.put(48,"Paragliding");
        types.put(49,"Pilates");
        types.put(50,"Polo");
        types.put(51,"Racquetball");
        types.put(52,"Rock climbing");
        types.put(53,"Rowing");
        types.put(54,"Rowing machine");
        types.put(55,"Rugby");
        types.put(8,"Running");
        types.put(56,"Jogging");
        types.put(57,"Running on sand");
        types.put(58,"Running (treadmill)");
        types.put(59,"Sailing");
        types.put(60,"Scuba diving");
        types.put(61,"Skateboarding");
        types.put(62,"Skating");
        types.put(63,"Cross skating");
        types.put(105,"Indoor skating");
        types.put(64,"Inline skating (rollerblading)");
        types.put(65,"Skiing");
        types.put(66,"Back-country skiing");
        types.put(67,"Cross-country skiing");
        types.put(68,"Downhill skiing");
        types.put(69,"Kite skiing");
        types.put(70,"Roller skiing");
        types.put(71,"Sledding");
        types.put(73,"Snowboarding");
        types.put(74,"Snowmobile");
        types.put(75,"Snowshoeing");
        types.put(120,"Softball");
        types.put(76,"Squash");
        types.put(77,"Stair climbing");
        types.put(78,"Stair-climbing machine");
        types.put(79,"Stand-up paddleboarding");
        types.put(3,"Still (not moving)");
        types.put(80,"Strength training");
        types.put(81,"Surfing");
        types.put(82,"Swimming");
        types.put(84,"Swimming (open water)");
        types.put(83,"Swimming (swimming pool)");
        types.put(85,"Table tennis (ping pong)");
        types.put(86,"Team sports");
        types.put(87,"Tennis");
        types.put(5,"Tilting (sudden device gravity change)");
        types.put(88,"Treadmill (walking or running)");
        types.put(4,"Unknown (unable to detect activity)");
        types.put(89,"Volleyball");
        types.put(90,"Volleyball (beach)");
        types.put(91,"Volleyball (indoor)");
        types.put(92,"Wakeboarding");
        types.put(7,"Walking");
        types.put(93,"Walking (fitness)");
        types.put(94,"Nording walking");
        types.put(95,"Walking (treadmill)");
        types.put(116,"Walking (stroller)");
        types.put(96,"Waterpolo");
        types.put(97,"Weightlifting");
        types.put(98,"Wheelchair");
        types.put(99,"Windsurfing");
        types.put(100,"Yoga");
        types.put(101,"Zumba");
        JSONObject json  = new JSONObject(responseBody);
        JSONArray sessions = json.getJSONArray("session");
        for(Object obj : sessions){
            JSONObject fields = (JSONObject) obj;
            if(types.get(fields.getInt("activityType"))!=null) {
                String startime = (String) fields.getString("startTimeMillis");
                start = new DateTime(Long.valueOf(startime));

                String endtime = (String) fields.getString("endTimeMillis");
                end = new DateTime(Long.valueOf(endtime));

                intervals.add(new AbstractMap.SimpleEntry<>(start,end));
            }
        }
        //System.out.println(sb);
        return intervals;
    }
}
