package jp.jprs.checkin;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Base64;
import java.util.Calendar;
import java.util.Collections;
import java.util.Date;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.concurrent.ConcurrentHashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import javax.mail.Address;
import javax.mail.Authenticator;
import javax.mail.Flags;
import javax.mail.Folder;
import javax.mail.Message;
import javax.mail.MessagingException;
import javax.mail.PasswordAuthentication;
import javax.mail.Session;
import javax.mail.Store;
import javax.mail.internet.MimeMultipart;

import com.fasterxml.jackson.core.type.TypeReference;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.SerializationFeature;

import jp.jprs.checkin.config.Config;
import jp.jprs.checkin.data.Absence;
import jp.jprs.checkin.data.WorkingStatus;
import jp.jprs.checkin.data.WorkingStatusInitialValue;

public class Checkin {

    /** 文字コード(MS932) */
    public static final String CHARSET = "MS932";
    /** 設定ファイル格納ディレクトリ */
    public static final String CONFIG_DIR = "config";
    /** 設定ファイル */
    public static final String CONFIG_FILE = CONFIG_DIR + "/config.json";
    /** 体制図ファイル(json) */
    public static final String STATUS_BACKUP_FILE = "status.json";
    /** 初期設定値ファイル */
    public static final String INITIAL_VALUE_FILE = "initialValue.txt";
    /** 管理者情報ファイル */
    public static final String MANAGERS_FILE = "managers.txt";
    /** 代替メールアドレス情報 */
    public static final String ALTERNATE_FILE = "alternate.bin";
    /** 不在情報ファイル */
    public static final String ABSENCE_FILE = "absence.json";
    /**  */
    public static final String MAIL_REJECT_LOG_FILE = "rejected.txt";

    /** アカウント名のパターン */
    protected static final Pattern accountPattern = Pattern.compile("\\[([A-Za-z0-9\\-]+)\\]");
    /** メールアドレスのパターン */
    protected static final Pattern mailaddressPattern = Pattern.compile("([A-Za-z0-9\\-_\\.]+@[A-Za-z0-9\\-_\\.]+)");
    /** 時間のフォーマット */
    protected static final SimpleDateFormat timeFormat = new SimpleDateFormat("HH:mm");
    /** 年月日・時間のフォーマット */
    protected static final SimpleDateFormat datetimeFormat = new SimpleDateFormat("yyyy/MM/dd HH:mm");

    protected static final String START_MARK = "[開始]";
    protected static final String END_MARK = "[終了]";
    protected static final String FIX_MARK = "[修正]";
    protected static final String CLEAR_MARK = "[クリア]";
    protected static final String AM_MARK = "AM";
    protected static final String PM_MARK = "PM";
    protected static final String TEL_MARK = "TEL";
    protected static final String ALT_MARK = "ALT";
    protected static final String REMORT_MARK = "[在宅]";
    protected static final String OFFICE_T_MARK = "[東京]";
    protected static final String OFFICE_O_MARK = "[大阪]";
    protected static final String GOOUT_MARK = "[外出]";
    protected static final String BT_MARK = "[出張]";
    protected static final String OFFDUTY = "[非番]";
    protected static final String VACATION_MARK = "[休暇]";
    protected static final String LEAVE_MARK = "[休職]";
    protected static final String TEL_EMBED_START = "[内線";
    protected static final String TEL_EMBED_END = "]";

    protected static final String ABSENCE_MARK = "[不在連絡]";
    protected static final String ABSENCE_PERSON_MARK = "不在者";
    protected static final String ABSENCE_PERIOD_MARK = "不在期間";
    protected static final String ABSENCE_REASON_MARK = "不在理由";
    protected static final String ABSENCE_TEL_MARK = "不在時TEL";
    protected static final String ABSENCE_RESET_MARK = "[不在連絡取消]";

    protected Config config;
    protected Calendar now;

    /** 体制図 */
    protected Map<String, WorkingStatus> status;
    /** 管理者マスタ */
    protected List<String> managers = new ArrayList<>();
    /** 代替メールアドレス(全量) */
    protected Map<String, List<String>> alternate;
    /** 代替メールアドレス(個人別) */
    protected Map<String, String> alternateR = new ConcurrentHashMap<>();
    /** 不在情報(個人別) */
    protected Map<String, List<Absence>> absence = new ConcurrentHashMap<>();
    /** 不在情報(全量) */
    protected Map<String, Map<String, List<Absence>>> absenceJ = new ConcurrentHashMap<>();
    /** 最終クリア日付 */
    protected int lastClearDay = 0;

    protected Path rejectLog = Paths.get(MAIL_REJECT_LOG_FILE);

    /**
     *
     * @param config 設定ファイル(config.json)の中身
     */
    protected void process(Config config) {
        this.config = config;

        try {

            // loadStatusメソッドを呼び出し、体制図をstatusに格納
            loadStatus(Paths.get(STATUS_BACKUP_FILE));

            // statusがnullの場合
            if (status == null) {
                // statusに空のmapを設定
                status = new ConcurrentHashMap<>();
            }

            // 各ファイルを読み込む
            loadInitialValue(Paths.get(INITIAL_VALUE_FILE));
            loadManagers(Paths.get(MANAGERS_FILE));
            loadAlternate(Paths.get(ALTERNATE_FILE));
            loadAbsence(Paths.get(ABSENCE_FILE));

        } catch (Throwable t) {
            t.printStackTrace();
        }

        // 以下無限ループ
        while (true) {

            // 処理時間計測スタート
            long start = System.currentTimeMillis();

            try {
                // 現在日時を取得し、カレンダー型に変換
                now = Calendar.getInstance();
                now.setTime(new Date());

                // TODO
                clear();

                Properties prop = new Properties();
                prop.setProperty("mail.pop3.host", config.getPop3server());
                prop.setProperty("mail.pop3.port", String.valueOf(config.getPop3port()));
                Authenticator authenticator = new Authenticator() {
                    protected PasswordAuthentication getPasswordAuthentication() {
                        return new PasswordAuthentication(config.getPop3account(), config.getPop3password());
                    }
                };

                Session session = Session.getInstance(prop, authenticator);
                Store store = session.getStore("pop3");
                store.connect();
                Folder inbox = store.getDefaultFolder().getFolder("INBOX");
                inbox.open(Folder.READ_WRITE);

                Message[] messages = inbox.getMessages();
                for (Message message : messages) {
                    processMessage(message);
                    inbox.setFlags(new Message[]{ message }, new Flags(Flags.Flag.DELETED), true);
                }

                inbox.close(true);
                store.close();

                write(Paths.get(config.getDstFile()), generate(false));
                saveStatus(Paths.get(STATUS_BACKUP_FILE));
                write(Paths.get(config.getDstAbsenceFile()), generateAbsence(false));
            } catch (Exception e) {
                e.printStackTrace();
            } catch (Throwable t) {
                t.printStackTrace();
            }

            // 処理時間計測ストップ
            long end = System.currentTimeMillis();

            try {
                Thread.sleep(config.getInterval() - end + start);
            } catch (InterruptedException e) {
            }
        }
    }

    protected void processMessage(Message message) throws MessagingException, IOException {
        Date date = message.getSentDate();
        Address[] address = message.getFrom();
        Matcher matF = mailaddressPattern.matcher(address[0].toString().toLowerCase());
        if (matF.find()) {
            String from = matF.group(1).toLowerCase();
            String[] returnPaths = message.getHeader("Return-Path");
            String returnPath = null;
            if (returnPaths != null && returnPaths[0].length() != 0) {
                Matcher matR = mailaddressPattern.matcher(returnPaths[0].toLowerCase());
                if (matR.find()) {
                    returnPath = matR.group(1).toLowerCase();
                }
            }
            if (returnPath == null || from.equals(returnPath) || managers.contains(returnPath)) {
                if (this.alternateR.get(from) != null) {
                    from = this.alternateR.get(from);
                }
                Object body = message.getContent();
                String bodyText = "";
                if (body instanceof String) {
                    bodyText = (String) body;
                } else if (body instanceof MimeMultipart) {
                    MimeMultipart multiBody = (MimeMultipart) body;
                    for (int i = 0; i < multiBody.getCount(); i++) {
                        if (multiBody.getBodyPart(i).getContentType() != null && multiBody.getBodyPart(i).getContentType().contains("text")) {
                            bodyText = multiBody.getBodyPart(i).getContent().toString();
                            break;
                        }
                    }
                }
                check(from, date, bodyText);
            } else {
                try {
                    Files.write(rejectLog, Arrays.asList(getTodayStr() + ", " + from + ", " + returnPath), Charset.forName(CHARSET), StandardOpenOption.APPEND);
                } catch (IOException e) {
                    e.printStackTrace();
                }                        }
        }
    }

    /**
     *
     */
    protected void clear() {

        // 日付を取得
        int day = now.get(Calendar.DAY_OF_MONTH);
        // 時間を取得(24時間制)
        int hour = now.get(Calendar.HOUR_OF_DAY);

        // 取得した日付が最終クリア日付と異なっている、かつ
        // 現在時刻が5時台である場合
        if (day != lastClearDay && hour == 5) {

            // writeメソッドを呼び出し、設定ファイルに記載のbackupDir(output/bk)に
            // 現在日付 - 1日のファイル名で””を書き込む
            // TODO
            write(Paths.get(config.getBackupDir(), genBackupFileName(now)), generate(true));

            saveStatus(Paths.get(config.getBackupDirJson(), genBackupJsonFileName(now)));

            status.clear();

            gcAbsence(now.getTime());

            loadInitialValue(Paths.get(INITIAL_VALUE_FILE));

            loadManagers(Paths.get(MANAGERS_FILE));

            lastClearDay = day;
        }
    }

    protected void check(String from, Date date, String body) {
        body = ms932(body);
        String[] lines = body.split("[\r\n]+");
        int i = 0;
        boolean skipped = false;
        String mark = "";
        boolean absence = false;
        while (!skipped && i < lines.length) {
            for (; i < lines.length; i++) {
                if (trim(lines[i]).startsWith(START_MARK)) {
                    mark = START_MARK;
                    break;
                } else if (trim(lines[i]).startsWith(END_MARK)) {
                    mark = END_MARK;
                    break;
                } else if (trim(lines[i]).startsWith(FIX_MARK)) {
                    mark = FIX_MARK;
                    break;
                } else if (trim(lines[i]).startsWith(CLEAR_MARK)) {
                    if (i == 0) {
                        getStatus(from, date).setFinished(false);
                        return;
                    }
                } else if (trim(lines[i]).startsWith(ABSENCE_MARK)) {
                    mark = ABSENCE_MARK;
                    absence = true;
                    break;
                } else if (trim(lines[i]).startsWith(ABSENCE_RESET_MARK)) {
                    mark = ABSENCE_RESET_MARK;
                    absence = true;
                    break;
                }
            }
            i++;
            if (i < lines.length) {
                if (!absence && (trim(lines[i]).startsWith(AM_MARK) || trim(lines[i]).startsWith(PM_MARK)
                        || trim(lines[i]).startsWith(TEL_MARK) || trim(lines[i]).startsWith(ALT_MARK))) {
                    skipped = true;
                } else if (absence && (trim(lines[i]).startsWith(ABSENCE_PERSON_MARK) || trim(lines[i]).startsWith(ABSENCE_PERIOD_MARK) ||
                        trim(lines[i]).startsWith(ABSENCE_REASON_MARK) || trim(lines[i]).startsWith(ABSENCE_TEL_MARK))) {
                    skipped = true;
                }
            }
        }
        WorkingStatus st;
        switch (mark) {
        case START_MARK:
            st = checkNormal(from, date, lines, i);
            st.setFinished(false);
            break;
        case END_MARK:
            st = checkNormal(from, date, lines, i);
            st.setFinished(true);
            break;
        case FIX_MARK:
            checkNormal(from, date, lines, i);
            break;
        case ABSENCE_MARK:
            checkAbsence(from, date, lines, i);
            break;
        case ABSENCE_RESET_MARK:
            resetAbsence(from, date, lines, i);
            break;
        default:
            getStatus(from, date);
            return;
        }
    }

    private WorkingStatus checkNormal(String from, Date date, String[] lines, int i) {
        WorkingStatus st = getStatus(from, date);
        List<String> alts = new ArrayList<>();
        for (; i < lines.length; i++) {
            String line = trim(lines[i]);
            if (line.startsWith(AM_MARK)) {
                String where = line.substring(AM_MARK.length());
                if (where.contains(REMORT_MARK) || where.contains(GOOUT_MARK) || where.contains(BT_MARK)) {
                    st.setStatusAM(WorkingStatus.Status.remote);
                } else if (where.contains(OFFICE_T_MARK) || where.contains(OFFICE_O_MARK)) {
                    st.setStatusAM(WorkingStatus.Status.office);
                } else if (where.contains(OFFDUTY)) {
                    st.setStatusAM(WorkingStatus.Status.offduty);
                } else if (where.contains(VACATION_MARK)) {
                    st.setStatusAM(WorkingStatus.Status.vacation);
                } else if (where.contains(LEAVE_MARK)) {
                    st.setStatusAM(WorkingStatus.Status.leave);
                } else {
                    st.setStatusAM(WorkingStatus.Status.contact);
                }
                st.setStatusAMText(getStatusText(where));
            } else if (line.startsWith(PM_MARK)) {
                String where = line.substring(PM_MARK.length());
                if (where.contains(REMORT_MARK) || where.contains(GOOUT_MARK) || where.contains(BT_MARK)) {
                    st.setStatusPM(WorkingStatus.Status.remote);
                } else if (where.contains(OFFICE_T_MARK) || where.contains(OFFICE_O_MARK)) {
                    st.setStatusPM(WorkingStatus.Status.office);
                } else if (where.contains(OFFDUTY)) {
                    st.setStatusPM(WorkingStatus.Status.offduty);
                } else if (where.contains(VACATION_MARK)) {
                    st.setStatusPM(WorkingStatus.Status.vacation);
                } else if (where.contains(LEAVE_MARK)) {
                    st.setStatusPM(WorkingStatus.Status.leave);
                } else {
                    st.setStatusPM(WorkingStatus.Status.contact);
                }
                st.setStatusPMText(getStatusText(where));
            } else if (line.startsWith(TEL_MARK)) {
                String number = getStatusText(line.substring(TEL_MARK.length()));
                st.setTel(number);
            } else if (line.startsWith(ALT_MARK)) {
                String alt = getStatusText(line.substring(ALT_MARK.length()));
                if (alt != null && alt.length() != 0) {
                    alts.addAll(Arrays.asList(alt.split("\\s*,\\s*")));
                }
            }
        }
        if (!alts.isEmpty()) {
            if (this.alternate.get(from) != null) {
                for (String a : this.alternate.get(from)) {
                    this.alternateR.remove(a);
                }
            }
            this.alternate.put(from, alts);
            for (String a : this.alternate.get(from)) {
                this.alternateR.put(a, from);
            }
            saveAlternate(Paths.get(ALTERNATE_FILE));
        }
        return st;
    }

    private WorkingStatus getStatus(String from, Date date) {
        WorkingStatus st = status.get(from);
        if (st == null) {
            st = new WorkingStatus().setStatusAM(WorkingStatus.Status.contact).setStatusPM(WorkingStatus.Status.contact);
            st.setFirstReceived(date);
            st.setLastReceived(null);
            status.put(from, st);
        } else {
            st.setLastReceived(date);
        }
        return st;
    }

    private void checkAbsence(String from, Date date, String[] lines, int i) {
        Absence ab = new Absence();
        ab.setReportedDate(date);
        if (from.contains("@")) {
            ab.setReported(from.substring(0, from.indexOf("@")));
        } else {
            ab.setReported(from);
        }
        String person = null;
        for (; i < lines.length; i++) {
            String line = trim(lines[i]);
            if (line.startsWith(ABSENCE_PERSON_MARK)) {
                person = getStatusText(line.substring(ABSENCE_PERSON_MARK.length()));
            } else if (line.startsWith(ABSENCE_PERIOD_MARK)) {
                String period = getStatusText(line.substring(ABSENCE_PERIOD_MARK.length()));
                ab.setPeriod(period);
            } else if (line.startsWith(ABSENCE_REASON_MARK)) {
                String where = line.substring(ABSENCE_REASON_MARK.length());
                if (where.contains(REMORT_MARK) || where.contains(GOOUT_MARK) || where.contains(BT_MARK)) {
                    ab.setStatus(WorkingStatus.Status.remote);
                } else if (where.contains(OFFICE_T_MARK) || where.contains(OFFICE_O_MARK)) {
                    ab.setStatus(WorkingStatus.Status.office);
                } else if (where.contains(OFFDUTY)) {
                    ab.setStatus(WorkingStatus.Status.offduty);
                } else if (where.contains(VACATION_MARK)) {
                    ab.setStatus(WorkingStatus.Status.vacation);
                } else if (where.contains(LEAVE_MARK)) {
                    ab.setStatus(WorkingStatus.Status.leave);
                } else {
                    ab.setStatus(WorkingStatus.Status.contact);
                }
                ab.setStatusText(getStatusText(where));
            } else if (line.startsWith(ABSENCE_TEL_MARK)) {
                String number = getStatusText(line.substring(ABSENCE_TEL_MARK.length()));
                ab.setTel(number);
            }
        }

        if (person != null && ab.isValid()) {
            if (!person.contains("@")) {
                person = person.toLowerCase() + "@jprs.co.jp";
            } else {
                person = person.toLowerCase();
            }
            Map<String, List<Absence>> map = this.absenceJ.get(ab.getReported());
            if (map == null) {
                map = new ConcurrentHashMap<>();
                this.absenceJ.put(ab.getReported(), map);
            }
            List<Absence> list = map.get(person);
            if (list == null) {
                list = new ArrayList<>();
                map.put(person, list);
            }
            list.add(ab);
            saveAbsence(Paths.get(ABSENCE_FILE));
            buildAbsence();
        }
    }

    private void resetAbsence(String from, Date date, String[] lines, int i) {
        String reported;
        if (from.contains("@")) {
            reported = from.substring(0, from.indexOf("@"));
        } else {
            reported = from;
        }
        String person = null;
        for (; i < lines.length; i++) {
            String line = trim(lines[i]);
            if (line.startsWith(ABSENCE_PERSON_MARK)) {
                person = getStatusText(line.substring(ABSENCE_PERSON_MARK.length()));
                break;
            }
        }

        if (person != null) {
            if (!person.contains("@")) {
                person = person.toLowerCase() + "@jprs.co.jp";
            } else {
                person = person.toLowerCase();
            }
            Map<String, List<Absence>> map = this.absenceJ.get(reported);
            if (map == null) {
                return;
            }
            List<Absence> list = map.get(person);
            if (list == null) {
                return;
            }
            map.remove(person);
            saveAbsence(Paths.get(ABSENCE_FILE));
            buildAbsence();
        }
    }

    protected String getStatusText(String line) {
        int begin = line.indexOf('[');
        int end = line.indexOf(']');
        if (0 <= begin && begin < line.length() - 1 && 0 <= end && end < line.length()) {
            return line.substring(begin + 1, end);
        }
        return line;
    }

    /**
     *
     * @param backup バックアップフラグ
     * @return dst 返却用HTML
     */
    protected String generate(boolean backup) {

        // 返却用HTML
        StringBuilder dst = new StringBuilder();

        // テンプレートファイル(template/taisei.html)を読み込み、readerに格納する
        try (BufferedReader reader
                = Files.newBufferedReader(Paths.get(config.getSrcFile()), Charset.forName(CHARSET))) {

            // 処理中の行
            String line;
            // 処理中 -1番目の行
            String prevLine = null;

            // テンプレートファイル(template/taisei.html)の終端まで繰り返す
            while ((line = reader.readLine()) != null) {

                Matcher mat1 = accountPattern.matcher(line);
                Matcher mat2 = mailaddressPattern.matcher(line);
                boolean byAccount = false;
                boolean byMailAddress = false;

                // 該当行にアカウント名が含まれている場合
                if (mat1.find()) {
                    // アカウントフラグを立てる
                    byAccount = true;
                }

                // 該当行にメールアドレスが含まれている場合
                if (mat2.find()) {
                    // メールアドレスアドレスフラグを立てる
                    byMailAddress = true;
                }

                // 該当行がアカウント名でもメールアドレスでもない場合
                if (!byAccount && !byMailAddress) {

                    // 該当行に"<body>"が含まれている場合
                    if (line.contains("<body>")) {

                        // 返却用HTMLに該当行 + 改行コードを追加する
                        dst.append(line).append("\r\n");

                        // 返却用HTMLに各開始タグを追加する
                        dst.append("<table border=\"0\" width=\"100%\"><tbody><tr><td align=\"left\"><a href=\"");

                        // バックアップフラグがtrueの場合
                        if (backup) {
                            // 返却用HTMLに以下のリンクを追加する
                            // 現在日時 -2日 の「←前日」ボタン、現在日時の「◆翌日→」ボタン
                            dst.append(genPrevBackupFileName(now))
                                .append("\">←前日</a>")
                                .append("◆<a href=\"")
                                .append(genNextBackupFileName(now))
                                .append("\">翌日→</a>");

                        // バックアップフラグがfalseの場合
                        } else {
                            // 返却用HTMLに以下のリンクを追加する
                            // 現在日時 -1日 の「←前日」ボタン
                            dst.append("bk/").append(genBackupFileName(now)).append("\">←前日</a>");
                        }

                        // 返却用HTMLにマニュアルへのリンクを追加する
                        dst.append( "</td>"
                                    + "<td align=\"right\">"
                                    + "<a href=\"http://docmgr.jprs.co.jp/evportal/document/vfdocument.aspx?did=277337&state=0&tab=1\" target=\"_blank\">マニュアル</a>"
                                    + "</td>"
                                    + "</tr></tbody></table>\r\n");

                        // 返却用HTMLに最終更新日時を追加する
                        dst.append("<table border=\"0\" width=\"100%\"><tbody><tr><td align=\"right\">最終更新日時(5分毎更新)：")
                            .append(getDatetime(now.getTime()))
                            .append("</td></tr></tbody></table>\r\n");

                        // 返却用HTMLに判例を追加する
                        dst.append("<table cellspacing=\"3\" width=\"40%\" align=\"right\">"
                                    + "<tbody><tr align=\"center\">"
                                    + "<td width=\"10%\" align=\"right\">凡例</td>"
                                    + "<td width=\"15%\" style='background:lime;'>会社</td>"
                                    + "<td width=\"15%\" style='background:aqua;'>在宅/外出/出張</td>"
                                    + "<td width=\"15%\" style='background:yellow;'>勤務終了</td>"
                                    + "<td width=\"15%\" style='background:gainsboro;'>休暇/非番/休職</td>"
                                    + "<td width=\"15%\" style='background:lightcyan;'>不明（更新あり）</td>"
                                    + "<td width=\"15%\" style='background:darkgray;'>不明（更新なし）</td>"
                                    + "</tr></tbody></table>");

                        // 前行にnullを設定する
                        prevLine = null;

                    // 該当行に"<body>"が含まれていないかつ、前行がnullでない場合
                    } else if (prevLine != null) {

                        // 返却用HTMLに前行+改行を追加する
                        dst.append(prevLine).append("\r\n");

                        // 前行に処理中の行を設定する
                        prevLine = line;

                    // 上記以外の場合
                    } else {

                        // 前行に処理中の行を設定する
                        prevLine = line;
                    }

                // 該当行にアカウント名、もしくはメールアドレスが含まれている場合
                } else {

                    // 対象者のメールアドレス
                    String account = "";

                    // アカウント名が含まれている場合
                    if (byAccount) {
                        // アカウント名を小文字に変換してメールアドレス形式として変数に格納する
                        account = mat1.group(1).toLowerCase() + "@jprs.co.jp";

                    // メールアドレスが含まれている場合
                    } else if (byMailAddress) {
                        // メールアドレスを小文字に変換して変数に格納する
                        account = mat2.group(1).toLowerCase();
                    }

                    // 対象者の勤怠情報を取得する
                    WorkingStatus status = this.status.get(account.toLowerCase());

                    // 勤怠情報がnullの場合
                    if (status == null) {

                        // 対象者の不在情報を取得する
                        status = getAbsenceStatus(account, now.getTime());
                    }
                    // 勤怠情報がnullの場合(不在情報も存在しない場合)
                    if (status == null) {

                        // 勤怠情報に"不明"を設定する
                        status = WorkingStatus.UNKNOWN;
                    }

                    // 前行の、先頭から数えて">"が出現する +1 番目
                    int nameFrom = prevLine.indexOf(">") + 1;

                    // 前行の、終端から数えて"<"が出現する番目
                    int nameTo = prevLine.lastIndexOf("<");

                    // 対象行の、先頭から数えて"["が出現する番目
                    int statusFollow = line.indexOf("[");

                    // 前行に">"が存在する
                    // 前行の途中に">"が存在する
                    // 前行に"<"が存在する
                    //TODO
                    // 前行が"<"で終了していない
                    // 対象行に"["が存在する
                    // 対象行が"["で終了していない
                    if (0 <= nameFrom
                            && nameFrom < prevLine.length()
                            && 0 <= nameTo
                            && nameTo < prevLine.length()
                            && 0 <= statusFollow
                            && statusFollow < line.length()) {

                        //
                        dst.append("      <td ").append(getStatus(status).style()).append(">")
                           .append(prevLine.substring(nameFrom, nameTo)).append("</td>").append("\r\n");

                        //
                        if (status.getAbsenceReported() == null || status.getAbsenceReported().length() == 0) {

                            //
                            if (!line.contains("colspan")) {

                                dst.append("      <td ")
                                    .append(getStatus(status).style())
                                    .append(">")
                                    .append(getStatusText(status))
                                    .append(embedString(line.substring(statusFollow), escape(status.getTel())))
                                    .append("\r\n");


                            } else {
                                dst.append("      <td colspan=\"2\" ")
                                    .append(getStatus(status).style()).append(">")
                                    .append(getStatusText(status))
                                    .append(embedString(line.substring(statusFollow), escape(status.getTel())))
                                    .append("\r\n");
                            }

                        //
                        } else {

                            //
                            if (!line.contains("colspan")) {

                                dst.append("      <td ")
                                    .append(getStatus(status).style()).append(">")
                                    .append(getStatusText(status))
                                    .append(embedString2(line.substring(statusFollow), escape(status.getTel()), "不在連絡：" + status.getAbsenceReported()))
                                    .append("\r\n");


                            } else {
                                dst.append("      <td colspan=\"2\" ")
                                    .append(getStatus(status).style())
                                    .append(">")
                                    .append(getStatusText(status))
                                    .append(embedString2(line.substring(statusFollow), escape(status.getTel()), "不在連絡：" + status.getAbsenceReported()))
                                    .append("\r\n");
                            }
                        }

                        prevLine = null;

                    //
                    } else {

                        if (prevLine != null) {

                            dst.append(prevLine);
                            dst.append("\r\n");
                        }

                        prevLine = line;
                    }
                }
            }
            //
            if (prevLine != null) {

                dst.append(prevLine);
                dst.append("\r\n");
            }

        } catch (Throwable t) {
            t.printStackTrace();
        }
        //
        return dst.toString();
    }

    protected String generateAbsence(boolean backup) {
        StringBuilder dst = new StringBuilder();
        try (BufferedReader reader = Files.newBufferedReader(Paths.get(config.getSrcFile()), Charset.forName(CHARSET))) {
            String line;
            String prevLine = null;
            while ((line = reader.readLine()) != null) {
                Matcher mat1 = accountPattern.matcher(line);
                Matcher mat2 = mailaddressPattern.matcher(line);
                boolean byAccount = false;
                boolean byMailAddress = false;
                if (mat1.find()) {
                    byAccount = true;
                }
                if (mat2.find()) {
                    byMailAddress = true;
                }
                if (!byAccount && !byMailAddress) {
                    if (line.contains("<body>")) {
                        dst.append(line).append("\r\n");
                        dst.append("<table border=\"0\" width=\"100%\"><tbody><tr><td align=\"right\">最終更新日時(5分毎更新)：").append(getDatetime(now.getTime())).append("</td></tr></tbody></table>\r\n");
                        prevLine = null;
                    } else if (prevLine != null) {
                        dst.append(prevLine).append("\r\n");
                        prevLine = line;
                    } else {
                        prevLine = line;
                    }
                } else {
                    String account = "";
                    if (byAccount) {
                        account = mat1.group(1).toLowerCase() + "@jprs.co.jp";
                    } else if (byMailAddress) {
                        account = mat2.group(1).toLowerCase();
                    }
                    String absenceStatus = "不在予定なし";
                    String absenceStatusStyle = "style='background:white;'";
                    List<Absence> absence = this.absence.get(account.toLowerCase());
                    if (absence != null && !absence.isEmpty()) {
                        absenceStatus = String.join(", ", absence.stream().map(entry->entry.toString()).collect(Collectors.toList()));
                        absenceStatusStyle = "style='background:gainsboro;'";
                    }

                    int nameFrom = prevLine.indexOf(">") + 1;
                    int nameTo = prevLine.lastIndexOf("<");
                    int statusFollow = line.indexOf("[");
                    if (0 <= nameFrom && nameFrom < prevLine.length() && 0 <= nameTo && nameTo < prevLine.length() && 0 <= statusFollow && statusFollow < line.length()) {
                        dst.append("      <td ").append(absenceStatusStyle).append(">")
                           .append(prevLine.substring(nameFrom, nameTo)).append("</td>").append("\r\n");
                        if (!line.contains("colspan")) {
                            dst.append("      <td ").append(absenceStatusStyle).append(">")
                               .append(embedString(line.substring(statusFollow), escape(absenceStatus))).append("\r\n");
                        } else {
                            dst.append("      <td colspan=\"2\" ").append(absenceStatusStyle).append(">")
                               .append(embedString(line.substring(statusFollow), escape(absenceStatus))).append("\r\n");
                        }
                        prevLine = null;
                    } else {
                        if (prevLine != null) {
                            dst.append(prevLine);
                            dst.append("\r\n");
                        }
                        prevLine = line;
                    }
                }
            }
            if (prevLine != null) {
                dst.append(prevLine);
                dst.append("\r\n");
            }
        } catch (Throwable t) {
            t.printStackTrace();
        }
        return dst.toString();
    }

    protected WorkingStatus.Status getStatus(WorkingStatus status) {
        if (status == null) {
            return WorkingStatus.Status.unknown;
        } else if (status.isFinished()) {
            return WorkingStatus.Status.home;
        }
        int hour = now.get(Calendar.HOUR_OF_DAY);
        if (hour <= 12) {
            return status.getStatusAM();
        } else {
            return status.getStatusPM();
        }
    }

    protected String getStatusText(WorkingStatus status) {
        if (status == null || status == WorkingStatus.UNKNOWN) {
            return "（" + WorkingStatus.Status.unknown.label() + "）";
        }
        StringBuilder text = new StringBuilder("（");
        if (status.getStatusAMText() != null) {
            if (status.getStatusAMText().length() <= 2) {
                text.append("AM").append(escape(status.getStatusAMText())).append(" ");
            } else {
                text.append("AM").append(escape(status.getStatusAMText().substring(0, 2))).append(" ");
            }
        } else {
            text.append("AM").append("-").append(" ");
        }
        if (status.getStatusPMText() != null) {
            if (status.getStatusPMText().length() <= 2) {
                text.append("PM").append(escape(status.getStatusPMText()));
            } else {
                text.append("PM").append(escape(status.getStatusPMText().substring(0, 2)));
            }
        } else {
            text.append("PM").append("-").append(" ");
        }
        if (status.getFirstReceived() != null) {
            text.append(" ").append(getTime(status.getFirstReceived()));
        }
        if (status.getLastReceived() != null) {
            text.append(" ").append(getTime(status.getLastReceived()));
        }
        if (status.isFinished()) {
            text.append(" 勤務終了");
        }
        text.append("）");
        return text.toString();
    }

    protected String embedString(String src, String...str) {
        if (str == null || str.length == 0 || str[0] == null) {
            return src;
        }
        int start = src.indexOf(TEL_EMBED_START);
        if (0 <= start && start <= src.length()) {
            int end = src.indexOf(TEL_EMBED_END, start);
            if (0 <= end && end <= src.length()) {
                return src.substring(0, start) + "[" + String.join("][", str) + "]" + src.substring(end + 1);
            }
        }
        return src;
    }

    protected String embedString2(String src, String...str) {
        if (str == null || str.length == 0) {
            return src;
        }
        int start = src.indexOf(TEL_EMBED_START);
        if (0 <= start && start <= src.length()) {
            int end = src.indexOf(TEL_EMBED_END, start);
            if (str[0] == null) {
                str[0] = src.substring(start + 1, end);
            }
            if (0 <= end && end <= src.length()) {
                return src.substring(0, start) + "[" + String.join("][", str) + "]" + src.substring(end + 1);
            }
        }
        return src;
    }

    protected String[] normalize(String...str) {
        return (String[]) Arrays.stream(str).map(elem->elem != null ? elem : "").toArray(String[]::new);
    }

    /**
     * 引数で渡されたDate型の日付を"yyyy/MM/dd HH:mm"形式に変換する
     * @param date
     * @return"yyyy/MM/dd HH:mm"形式
     */
    protected String getDatetime(Date date) {
        return datetimeFormat.format(date);
    }

    /**
     * 引数で渡された文字列の日付を"yyyy/MM/dd HH:mm"形式に変換する
     * @param date
     * @return "yyyy/MM/dd HH:mm"形式
     * @throws ParseException
     */
    protected Date getDatetime(String date) throws ParseException {
        return datetimeFormat.parse(date);
    }

    protected String getTime(Date date) {
        return timeFormat.format(date);
    }

    /**
     * 引数で渡されたパスのファイルに <br>
     * 引数で渡された文字列を書き込む
     * @param path ファイルパス
     * @param text 書き込む内容
     */
    protected void write(Path path, String text) {

        // 引数で渡されたパスのファイルにtextを書き込む
        try (BufferedWriter writer = Files.newBufferedWriter(path, Charset.forName(CHARSET))) {
            writer.write(text);
            writer.flush();
        } catch (Throwable t) {
            t.printStackTrace();
        }
    }

    protected void saveStatus(Path path) {
        try (BufferedWriter writer = Files.newBufferedWriter(path, Charset.forName(CHARSET))) {
            ObjectMapper mapper = new ObjectMapper().enable(SerializationFeature.INDENT_OUTPUT);
            writer.write(mapper.writeValueAsString(status));
        } catch (Throwable t) {
            t.printStackTrace();
        }
    }

    /**
     * 体制図ファイルを読み込み、map形式に変換する
     * @param path 体制図のパス(status.json)
     */
    protected void loadStatus(Path path) {

        // 体制図ファイルを読み込む
        try (BufferedReader reader = Files.newBufferedReader(path, Charset.forName(CHARSET))) {
            ObjectMapper mapper = new ObjectMapper();

            // 読み込んだjsonファイルをmap形式に変換する
            status = mapper.readValue(reader, new TypeReference<ConcurrentHashMap<String, WorkingStatus>>() {});

            // 変換後のmapがnullの場合
            if (status == null) {
                // 空のmapを生成する
                status = new ConcurrentHashMap<>();
            }

        } catch (Throwable t) {
            t.printStackTrace();
        }
    }

    /**
     * 初期設定値ファイルを読み込み、map形式に変換する <br>
     * 現在時点で非番、長期休暇、休業者がいる場合、体制図mapに該当する要素を追加する
     * @param path 初期設定値ファイルのパス(initialValue.txt)
     */
    protected void loadInitialValue(Path path) {

        // 初期設定値ファイルを読み込む
        try (BufferedReader reader = Files.newBufferedReader(path, Charset.forName(CHARSET))) {
            StringBuilder jsonText = new StringBuilder();
            String line;

            // 初期設定値ファイルの終端まで以下の処理を繰り返す
            while ((line = reader.readLine()) != null) {

                // 最初の文字が#でない(コメントアウトの行でない)場合
                if (!line.startsWith("#")) {
                    // json形式として1行変数に書き込む
                    jsonText.append(line);
                }
            }

            ObjectMapper mapper = new ObjectMapper();

            // 初期設定値ファイルのjson部分をmap形式に変換する
            Map<String, WorkingStatusInitialValue> initialValue
                = mapper.readValue(
                        jsonText.toString(), new TypeReference<ConcurrentHashMap<String, WorkingStatusInitialValue>>() {});

            // 変換後の初期設定値ファイルがnullでない場合
            if (initialValue != null) {

                // mapの要素数分、以下の処理を繰り返す
                for (Map.Entry<String, WorkingStatusInitialValue> entry : initialValue.entrySet()) {

                    try {
                        // 現在日時を取得
                        Date now = new Date();
                        // 初期設定値ファイルの"dateFrom"要素を日付型に変換
                        Date from = getDatetime(entry.getValue().getDateFrom() + " 00:00");
                        // 初期設定値ファイルの"dateTo"要素を日付型に変換
                        Date to = getDatetime(entry.getValue().getDateTo() + " 23:59");

                        // "dateFrom"要素 ＜ 現在日時 ＜ "dateTo"要素が成り立つ場合
                        if (now.after(from) && now.before(to)) {
                            // 体制図mapに該当する要素を追加する
                            status.put(entry.getKey(), entry.getValue());
                        }
                    } catch (Exception e) {
                        e.printStackTrace();
                    }
                }
            }
        } catch (Throwable t) {
            t.printStackTrace();
        }
    }

    /**
     * 管理者マスタファイルを読み込み、managersリストに変換する <br>
     * "xxx@jprs.co.jp"の形式で格納
     * @param path 管理者マスタファイルのパス(managers.txt)
     */
    protected void loadManagers(Path path) {

        // managersリストの全ての要素を削除
        managers.clear();

        // 管理者マスタファイルを読み込む
        try (BufferedReader reader = Files.newBufferedReader(path, Charset.forName(CHARSET))) {

            String line;

            // 管理者マスタファイルの終端まで以下の処理を繰り返す
            while ((line = reader.readLine()) != null) {

                // 最初の文字が#でない(コメントアウトの行でない)場合
                if (!line.startsWith("#")) {
                    // "@"を含む場合
                    if (line.contains("@")) {
                        // 該当行の大文字を小文字に変換してmanagersリストに追加する
                        managers.add(line.toLowerCase());

                    // "@"を含まない場合
                    } else if (line.length() != 0) {
                        // 該当行の大文字を小文字に変換し、"@jprs.co.jp"を結合させた文字列を
                        // managersリストに追加する
                        managers.add(line.toLowerCase() + "@jprs.co.jp");
                    }
                }
            }
        } catch (Throwable t) {
            t.printStackTrace();
        }
    }

    /**
     * 代替メールアドレス情報を読み込み、alternate(全量)、alternateR(個人別)に格納する <br>
     * @param path 代替メールアドレス情報のパス(alternate.bin)
     */
    protected void loadAlternate(Path path) {

        try {
            ObjectMapper mapper = new ObjectMapper();

            //TODO コンパイルエラー

            // 代替メールアドレス情報をBase64でデコードし、map形式に変換する
//            this.alternate
//                = mapper.readValue(Base64.getUrlDecoder().decode(Files.readAllBytes(path)),
//                        new TypeReference<ConcurrentHashMap<String, ArrayList<String>>>() {});

            // 代替メールアドレス(個人用)mapをクリア
            this.alternateR.clear();

            // 代替メールアドレス(全量)mapの要素数分以下の処理を繰り返す
            for (Map.Entry<String, List<String>> entry : this.alternate.entrySet()) {

                // 代替メールアドレス(全量)map要素のlist要素分以下の処理を繰り返す
                for (String a : entry.getValue()) {

                    // 代替メールアドレス(個人用)mapに値を追加する
                    this.alternateR.put(a, entry.getKey());
                }
            }
        } catch (Throwable t) {
            t.printStackTrace();
            this.alternate = new ConcurrentHashMap<>();
        }
    }

    protected void saveAlternate(Path path) {
        try {
            ObjectMapper mapper = new ObjectMapper();
            Files.write(path, Base64.getUrlEncoder().encode(mapper.writeValueAsBytes(this.alternate)));
        } catch (Throwable t) {
            t.printStackTrace();
        }
    }

    /**
     * 引数で渡された対象者の不在情報を取得し返却する <br>
     * 存在しない場合nullを返却する
     * @param account 対象者のメールアドレス
     * @param date 現在日時
     * @return 勤怠情報
     */
    protected WorkingStatus getAbsenceStatus(String account, Date date) {

        // 不在情報(個人別)から対象者の情報を取得する
        List<Absence> list = this.absence.get(account);

        // 不在情報が存在する場合
        if (list != null) {

            // 不在情報の数分繰り返す
            for (Absence ab: list) {

                // 不在情報から勤怠情報を取得する
                WorkingStatus st = ab.getStatus(date);

                // 勤怠情報がnullでない場合
                if (st != null) {
                    // 取得した勤怠情報を返却する
                    return st;
                }
            }
        }

        // 上記に当てはまらない場合、nullを返却する
        return null;
    }

    /**
     * 不在情報を読み込み、分割・ソートを実施するメソッドを呼び出す
     * @param path 不在情報のパス(absence.json)
     */
    protected void loadAbsence(Path path) {

        try {
            ObjectMapper mapper = new ObjectMapper();

            //TODO コンパイルエラー

            // 不在情報を読み込み、map形式に変換する
//            this.absenceJ = mapper.readValue(Files.readAllBytes(path),
//                    new TypeReference<ConcurrentHashMap<String, ConcurrentHashMap<String, ArrayList<Absence>>>>() {});

            // 不在情報を個人別に分割する
            buildAbsence();

        } catch (Throwable t) {
            t.printStackTrace();
            this.absenceJ = new ConcurrentHashMap<>();
            this.absence = new ConcurrentHashMap<>();
        }
    }

    protected void saveAbsence(Path path) {
        try {
            ObjectMapper mapper = new ObjectMapper();
            Files.write(path, mapper.writeValueAsBytes(this.absenceJ));
        } catch (Throwable t) {
            t.printStackTrace();
        }
    }

    protected void gcAbsence(Date date) {
        synchronized (this.absenceJ) {
            try {
                Map<String, Map<String, List<Absence>>> absenceJ = new ConcurrentHashMap<>();
                for (Map.Entry<String, Map<String, List<Absence>>> entry : this.absenceJ.entrySet()) {
                    Map<String, List<Absence>> newMap = new ConcurrentHashMap<>();
                    for(Map.Entry<String, List<Absence>> ent : entry.getValue().entrySet()) {
                        List<Absence> newList = new ArrayList<>();
                        for (Absence ab : ent.getValue()) {
                            if (!ab.getTo().before(date)) {
                                newList.add(ab);
                            }
                        }
                        if (!newList.isEmpty()) {
                            newMap.put(ent.getKey(), newList);
                        }
                    }
                    if (!newMap.isEmpty()) {
                        absenceJ.put(entry.getKey(), newMap);
                    }
                }
                this.absenceJ.clear();
                this.absenceJ = absenceJ;
                buildAbsence();
            } catch (Throwable t) {
                t.printStackTrace();
            }
        }
    }

    /**
     * 不在情報を個人別に分割し、日付でソートする
     */
    protected void buildAbsence() {
        synchronized (this.absence) {
            try {
                // 不在情報(個人別)をクリア
                this.absence.clear();

                // 不在情報(全量)の要素数分以下を繰り返す
                for (Map.Entry<String, Map<String, List<Absence>>> entry : this.absenceJ.entrySet()) {

                    // 不在情報(全量)の要素のmap要素分以下の処理を繰り返す
                    for(Map.Entry<String, List<Absence>> ent : entry.getValue().entrySet()) {

                        // 不在情報(個人別)のキーを取得(個人名)し、listに格納する
                        List<Absence> list = this.absence.get(ent.getKey());

                        // listがnullの場合
                        if (list == null) {
                            // 空のlistを生成し、不在情報(個人別)に設定する
                            list = new ArrayList<>();
                            this.absence.put(ent.getKey(), list);
                        }
                        // listに不在情報を設定する
                        list.addAll(ent.getValue());
                    }
                }

                // 不在情報(個人別)の要素数分以下を繰り返す
                for (List<Absence> list : this.absence.values()) {
                    // 不在日付が古い順にソートする
                    Collections.sort(list, (e1, e2)->e1.getReportedDate().before(e2.getReportedDate()) ? 1 : -1);
                }
            } catch (Throwable t) {
                t.printStackTrace();
            }
        }
    }

    /**
     * 現在日時 -1日を求める
     * @param cal 現在日時
     * @return "yyyyMMDD.html"
     */
    protected String genBackupFileName(Calendar cal) {

        Calendar cal0 = Calendar.getInstance();
        cal0.setTime(cal.getTime());

        // 現在日付 -1日 を設定する
        cal0.add(Calendar.DAY_OF_MONTH, -1);

        // 現在日時 -1日を"yyyyMMDD.html"形式に変換して返却
        return String.format(
                "%1$04d%2$02d%3$02d",
                cal0.get(Calendar.YEAR), cal0.get(Calendar.MONTH) + 1, cal0.get(Calendar.DAY_OF_MONTH)) + ".html";
    }

    /**
     * 現在日時 -2日を求める
     * @param cal 現在日時
     * @return "yyyyMMDD.html"
     */
    protected String genPrevBackupFileName(Calendar cal) {

        Calendar cal0 = Calendar.getInstance();
        cal0.setTime(cal.getTime());

        // 現在日付 -2日 を設定する
        cal0.add(Calendar.DAY_OF_MONTH, -2);

        // 現在日時 -2日を"yyyyMMDD.html"形式に変換して返却
        return String.format(
                "%1$04d%2$02d%3$02d",
                cal0.get(Calendar.YEAR), cal0.get(Calendar.MONTH) + 1, cal0.get(Calendar.DAY_OF_MONTH)) + ".html";
    }

    /**
     * 現在日時を求める
     * @param cal 現在日時
     * @return "yyyyMMDD.html"
     */
    protected String genNextBackupFileName(Calendar cal) {

        // 現在日時を"yyyyMMDD.html"形式に変換して返却
        return String.format(
                "%1$04d%2$02d%3$02d",
                cal.get(Calendar.YEAR), cal.get(Calendar.MONTH) + 1, cal.get(Calendar.DAY_OF_MONTH)) + ".html";
    }


    protected String genBackupJsonFileName(Calendar cal) {
        Calendar cal0 = Calendar.getInstance();
        cal0.setTime(cal.getTime());
        cal0.add(Calendar.DAY_OF_MONTH, -1);
        return String.format("%1$04d%2$02d%3$02d", cal0.get(Calendar.YEAR), cal0.get(Calendar.MONTH) + 1, cal0.get(Calendar.DAY_OF_MONTH)) + ".json";
    }

    protected String getTodayStr() {
        return String.format("%1$04d/%2$02d/%3$02d", now.get(Calendar.YEAR), now.get(Calendar.MONTH) + 1, now.get(Calendar.DAY_OF_MONTH)) + ".json";
    }

    protected String trim(String text) {
        return text.replaceAll("^\\s+", "");
    }

    protected static String ms932(String text) {
        return text
                .replaceAll("\\u2014", "\u2015")
                .replaceAll("\\u301c", "\uff5e")
                .replaceAll("\\u2016", "\u2225")
                .replaceAll("\\u2212", "\uff0d")
                .replaceAll("\\u00a2", "\uffe0")
                .replaceAll("\\u00a3", "\uffe1")
                .replaceAll("\\u00ac", "\uffe2");
    }

    protected static String escape(String src) {
        if (src != null) {
            return src.replaceAll("&", "&amp;")
                      .replaceAll("<", "&lt;")
                      .replaceAll(">", "&gt;")
                      .replaceAll("\"", "&quote;")
                      .replaceAll("'", "&#39;")
                      .replaceAll(" ", "&nbsp;")
                      .replaceAll("&amp;nbsp;", "&nbsp;")
                      .replaceAll("&amp;ensp;", "&ensp;")
                      .replaceAll("&amp;emsp;", "&emsp;")
                      .replaceAll("&amp;thinsp;", "&thinsp;");
        } else {
            return null;
        }
    }

    /**
     * メインメソッド
     * 設定ファイルを読み込んでprocessメソッドを呼び出す
     * @param args 使用しない
     */
    public static void main(String...args) {
        ObjectMapper mapper = new ObjectMapper();

        // 設定ファイルを読み込む
        try (InputStream in = Files.newInputStream(Paths.get(CONFIG_FILE))) {

            // json形式の設定をConfig型に変換
            Config config = mapper.readValue(in, Config.class);

            // processメソッドの引数に設定して呼び出す
            Checkin main = new Checkin();
            main.process(config);

        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
